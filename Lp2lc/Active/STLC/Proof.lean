import Mathlib.Tactic
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.Def

/-!
This file proves soundness for simply typed lambda calculus by interpreting
terms with a step-indexed logical relation. The step index is the fuel used to
reason about functions recursively: a function is safe for `steps` when, for
any `smaller_steps ≤ steps`, it sends semantically safe inputs to outputs that
stay safe one guarded step later.

All docstrings use tiny Scala-style STLC phrases as demonstrations.
-/

namespace Lp2lc.Active.STLC

/--
Step-indexed logical relation describing semantically well-behaved values.
At base type there is nothing extra to check. At function type, the relation is
guarded by the step index: if a function is valid for `steps`, then at any
smaller index it must send valid inputs to outputs that become valid later.

```scala
f(a)
```

The relation explains when applying `f` to a semantically valid `a` stays safe.
Safety of a function is therefore expressed by what happens when it is called.


TODO: return True if the interpreter can compute or use any value v of given type

AKA well-formedness
-/
def Semantics (type : Ty) (steps : Nat) (v : type.Denotation) : Prop :=
  match type with
  | .base => True
  | .arrow input output =>
      ∀ smaller_steps, smaller_steps ≤ steps →
        ∀ (vIn : input.Denotation), Semantics input smaller_steps vIn →
          Later (Semantics output smaller_steps (v vIn))

/--
Shrinking the step index preserves semantic validity of a value.
This is the monotonicity expected from a step-indexed argument: surviving more
steps is stronger than surviving fewer steps.

```scala
x => x
```

If the identity function is semantically valid for a larger budget, it stays
valid for every smaller budget as well. The syntax does not change, only the
amount of fuel we allow ourselves to inspect.
-/
lemma Semantics.monotone {type : Ty} {smaller_steps steps : Nat} {value : type.Denotation}
    (bound : smaller_steps ≤ steps)
    : Semantics type steps value → Semantics type smaller_steps value
    := by
  induction type generalizing smaller_steps steps with
  | base =>
      intro value_semantics
      simp [Semantics]
  | arrow input output _ _ =>
      intro function_semantics
      have function_semantics' :
          ∀ test_steps, test_steps ≤ steps →
            ∀ test_value, Semantics input test_steps test_value →
              Later (Semantics output test_steps (value test_value)) := by
        simpa [Semantics] using function_semantics
      change
        ∀ test_steps, test_steps ≤ smaller_steps →
          ∀ test_value, Semantics input test_steps test_value →
            Later (Semantics output test_steps (value test_value))
      intro test_steps test_bound test_value test_semantics
      exact function_semantics' test_steps (Nat.le_trans test_bound bound) test_value test_semantics

/--
Requires every variable in an environment to denote a semantically valid value.
This upgrades an ordinary valuation into one that is compatible with the
logical relation at a chosen step index.

```scala
f(a)
```

To reason about this open term, the environment must provide semantically valid
meanings for both `f` and `a`.
-/
def EnvSemantics (evaluator : Evaluator) (steps : Nat) : Prop :=
  ∀ (name : Var) (type : Ty) (binding : evaluator.env.get name = some type),
    Semantics type steps (evaluator.lookup name type binding)

/--
Environment semantics is also preserved when the step index decreases.
This is the environment-level version of `Semantics.monotone`: every binding in
the valuation remains semantically valid after reducing the step budget.

```scala
f(a)
```

If the meanings of `f` and `a` are valid for more steps, they are valid for
fewer too.
-/
lemma EnvironmentSemantics.monotone
    {evaluator : Evaluator} {smaller_steps steps : Nat}
    (bound : smaller_steps ≤ steps) :
    EnvSemantics evaluator steps → EnvSemantics evaluator smaller_steps := by
  intro evaluator_semantics name type binding
  exact Semantics.monotone bound (evaluator_semantics name type binding)

/--
Extending a semantically valid environment with a valid value preserves validity.
This is the semantic bookkeeping needed for lambdas: once a new argument value
is known to satisfy the relation, the extended environment is still sound.

```scala
x => f(x)
```

Inside the body, `x` is handled by the new binding introduced by the lambda,
while `f` still comes from the older environment. `extend_semantics` proves
that both sources of information coexist correctly.
-/
lemma extend_semantics {input : Ty} {steps : Nat} {evaluator : Evaluator}
    (evaluator_semantics : EnvSemantics evaluator steps)
    {name : Var} {value : input.Denotation} (value_semantics : Semantics input steps value) :
    EnvSemantics (evaluator.extend name value) steps := by
  intro tested_name type binding
  by_cases same_name : tested_name = name
  · subst same_name
    simp at binding ⊢
    cases binding
    simpa using value_semantics
  · have tail_binding : evaluator.env.get tested_name = some type := by
      simpa [same_name] using binding
    simpa [same_name] using
      evaluator_semantics tested_name type tail_binding


/--
Every scoped term denotes a value satisfying the logical relation at every step index.
This is the fundamental theorem of logical relations for the development. The
proof follows the syntax of terms: variables use the environment hypothesis,
lambdas extend the environment, and applications consume the function case.

```scala
x => f(x)
```

Once the environment gives semantically valid meanings to the free variables,
the whole term denotes a semantically valid value. In the example, it is enough
for the environment to supply a valid meaning for `f`; the bound `x` is handled
by the lambda case itself.
-/
theorem fundamental {type : Ty} (evaluator : Evaluator) (term : ScopedTerm evaluator.env type) :
    ∀ {steps : Nat},
      EnvSemantics evaluator steps →
      Semantics type steps (evaluator.denote term) := by
  rcases term with ⟨term, hscoped⟩
  revert evaluator
  induction term with
  | term_variable name =>
      intro evaluator hscoped steps evaluator_semantics
      simpa [Evaluator.denote] using evaluator_semantics name _ hscoped
  | unit =>
      intro evaluator hscoped steps evaluator_semantics
      simp [Semantics]
  | @lambda output input name body induction_hypothesis =>
      intro evaluator hscoped steps evaluator_semantics
      have body_scoped : IsScoped ((name, input) :: evaluator.env) body := by
        simpa using hscoped
      change
        ∀ smaller_steps, smaller_steps ≤ steps →
          ∀ value, Semantics input smaller_steps value →
            Later (Semantics output smaller_steps
              ((evaluator.denote ⟨Term.lambda name body, hscoped⟩) value))
      intro smaller_steps smaller_bound value value_semantics
      refine ⟨?_⟩
      simpa [Evaluator.denote] using
        induction_hypothesis
          (evaluator := evaluator.extend (input := input) name value)
          body_scoped
          (steps := smaller_steps)
          (extend_semantics
            (EnvironmentSemantics.monotone smaller_bound evaluator_semantics)
            value_semantics)
  | @apply input output function argument function_induction argument_induction =>
      intro evaluator hscoped steps evaluator_semantics
      have function_semantics :
          ∀ smaller_steps, smaller_steps ≤ steps →
            ∀ value, Semantics input smaller_steps value →
              Later
                (Semantics output smaller_steps
                  ((evaluator.denote ⟨function, hscoped.left⟩) value)) := by
        simpa [Semantics] using function_induction
          (evaluator := evaluator)
          hscoped.left
          (steps := steps)
          evaluator_semantics
      have argument_semantics :
          Semantics input steps (evaluator.denote ⟨argument, hscoped.right⟩) :=
        argument_induction
          (evaluator := evaluator)
          hscoped.right
          (steps := steps)
          evaluator_semantics
      simpa [Evaluator.denote] using
        (function_semantics steps le_rfl
          (evaluator.denote ⟨argument, hscoped.right⟩) argument_semantics).force

abbrev closed (type : Ty) := ScopedTerm [] type

/--
A closed term is semantically sound in the empty environment at every step index.
This packages the fundamental theorem for programs without free variables, so no
external assumptions remain.

```scala
x => x
```

Because this term is closed, it is semantically valid under the empty evaluator
for any number of steps. No external lookup is needed, since the only `x` is
bound inside the term itself.
-/
theorem soundness {type : Ty} (term : closed type) :
    ∀ steps, Semantics type steps (Evaluator.empty.denote term) := by
  intro steps
  exact fundamental Evaluator.empty term (steps := steps) (by
      intro name inner_type binding
      simp at binding)

end STLC
