import Mathlib.Tactic
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.Def

/-!
This file proves soundness for simply typed lambda calculus by interpreting
terms with a step-indexed logical relation. The step index is the fuel used to
reason about functions recursively: a function is safe for `fuel` when, for
any `lessFuel ≤ fuel`, it sends semantically safe inputs to outputs that
stay safe one guarded step later.

All docstrings use tiny Scala-style STLC phrases as demonstrations.
-/

namespace Lp2lc.Active.STLC

/--
Step-indexed logical relation describing semantically well-behaved (AKA well-formed) values.
return True if the interpreter can compute or use `v` at runtime

- Value of base type is always valid.
- Value of function type is true if its output can be consistently proven to be valid later, when it is called,
  on an input that is already valid. E.g.

  ```scala
  val fn = {x: Int => x + 1}
  ```

  is only valid if given arbitrary valid expression `(expression): Int`, `fn(expression)` is also valid

this Prop is guarded by the step-index: if a function is valid for `fuel`, then at any
smaller index it must send valid inputs to outputs that become valid later. E.g.
-/
def Semantics (type : Ty) (fuel : Nat) (v : type.Denotation) : Prop :=
  match type with
  | .base => True
  | .arrow input output =>
      let fn := v
      ∀ lessFuel, lessFuel ≤ fuel →
        ∀ (vIn : input.Denotation), Semantics input lessFuel vIn → -- input can be a function but has to be evaluated immediately
          Later (Semantics output lessFuel (fn vIn)) -- output can be evaluated later

/--
If a value works with a larger fuel budget, it also works with a smaller one.

```scala
val id = { x: Int => x }
```

If `id` is safe to call when we allow more runtime steps, it stays safe when we
check it with fewer steps. The function itself does not change; only the fuel
number gets smaller.
-/
lemma Semantics.monotone {fuel lessFuel : Nat} (bound : lessFuel ≤ fuel)
    {value : type.Denotation}
    : Semantics type fuel value → Semantics type lessFuel value
    := by
  induction type generalizing lessFuel fuel with
  | base =>
      intro value_semantics
      simp [Semantics]
  | arrow input output _ _ =>
      intro function_semantics
      have function_semantics' :
          ∀ test_fuel, test_fuel ≤ fuel →
            ∀ test_value, Semantics input test_fuel test_value →
              Later (Semantics output test_fuel (value test_value)) := by
        simpa [Semantics] using function_semantics
      change
        ∀ test_fuel, test_fuel ≤ lessFuel →
          ∀ test_value, Semantics input test_fuel test_value →
            Later (Semantics output test_fuel (value test_value))
      intro test_fuel test_bound test_value test_semantics
      exact function_semantics' test_fuel (Nat.le_trans test_bound bound) test_value test_semantics

/--
Return true if `Semantics` holds for every variable in an environment
-/
def REPLSemantics (repl : REPL) (fuel : Nat) : Prop :=
  ∀ (name : Var) (type : Ty) (binding : repl.env.get name = some type),
    Semantics type fuel (repl.varLookup name type binding)

/--
Similar to `Semantics.monotone`, but for every variable in an environment
-/
lemma REPLSemantics.monotone {repl : REPL} {lessFuel fuel : Nat}
    (bound : lessFuel ≤ fuel) :
    REPLSemantics repl fuel → REPLSemantics repl lessFuel := by
  intro repl_semantics name type binding
  exact Semantics.monotone bound (repl_semantics name type binding)

/--
If all inputs are semantically valid, adding one extra binding to an existing REPL will not change its validity. E.g. if

```scala
val x = 1
val y = x + 1
```

can be interpreted safely, then interpreting

```scala
val z = x + y
```

will also be safe.
-/
lemma REPLSemantics.extend {input : Ty} {fuel : Nat} {repl : REPL} {name : Var} {value : input.Denotation}
    (old_repl_semantics : REPLSemantics repl fuel) (extra : Semantics input fuel value) :
    REPLSemantics (repl.extend name value) fuel := by
  intro tested_name type binding
  by_cases same_name : tested_name = name
  · subst same_name
    simp at binding ⊢
    cases binding
    simpa using extra
  · have tail_binding : repl.env.get tested_name = some type := by
      simpa [same_name] using binding
    simpa [same_name] using
      old_repl_semantics tested_name type tail_binding

/--
If every outside name already points to a safe runtime value, then running the
whole program also gives a safe runtime value.

```scala
x => f(x)
```

Here the program only needs the outside world to supply a safe value for `f`.
The call later supplies `x`, and the result still behaves correctly.
-/
theorem fundamental (repl : REPL) (term : repl.env.ScopedTerm type) :
    ∀ {fuel : Nat},
      REPLSemantics repl fuel →
      Semantics type fuel (repl.eval term) := by
  rcases term with ⟨term, hscoped⟩
  revert repl
  induction term with
  | term_variable name =>
      intro repl hscoped fuel repl_semantics
      simpa [REPL.eval] using repl_semantics name _ hscoped
  | unit =>
      intro repl hscoped fuel _repl_semantics
      simp [Semantics]
  | @lambda output input name body induction_hypothesis =>
      intro repl hscoped fuel repl_semantics
      have body_scoped : (show Env from ((name, input) :: repl.env)).IsScoped body := by
        simpa using hscoped
      change
        ∀ lessFuel, lessFuel ≤ fuel →
          ∀ value, Semantics input lessFuel value →
            Later (Semantics output lessFuel
              ((repl.eval ⟨Term.lambda name body, hscoped⟩) value))
      intro lessFuel smaller_bound value value_semantics
      refine ⟨?_⟩
      simpa [REPL.eval] using
        induction_hypothesis
          (repl := repl.extend (input := input) name value)
          body_scoped
          (fuel := lessFuel)
          ((REPLSemantics.monotone smaller_bound repl_semantics).extend
            value_semantics)
  | @apply input output function argument function_induction argument_induction =>
      intro repl hscoped fuel repl_semantics
      have function_semantics :
          ∀ lessFuel, lessFuel ≤ fuel →
            ∀ value, Semantics input lessFuel value →
              Later
                (Semantics output lessFuel
                  ((repl.eval ⟨function, hscoped.left⟩) value)) := by
        simpa [Semantics] using function_induction
          (repl := repl)
          hscoped.left
          (fuel := fuel)
          repl_semantics
      have argument_semantics :
          Semantics input fuel (repl.eval ⟨argument, hscoped.right⟩) :=
        argument_induction
          (repl := repl)
          hscoped.right
          (fuel := fuel)
          repl_semantics
      simpa [REPL.eval] using
        (function_semantics fuel le_rfl
          (repl.eval ⟨argument, hscoped.right⟩) argument_semantics).force

abbrev closed (type : Ty) := Env.empty.ScopedTerm type

/--
A program with no outside names is safe to run from scratch for any fuel budget.

```scala
val id = { x: Int => x }
```

This program does not read anything preloaded. Its only `x` comes from the call
itself, so starting with an empty set of names is enough.
-/
theorem soundness {type : Ty} (term : closed type) :
    ∀ fuel, Semantics type fuel (REPL.empty.eval term) := by
  intro fuel
  exact fundamental REPL.empty term (fuel := fuel) (by
      intro _name _inner_type binding
      simp at binding)

end STLC
