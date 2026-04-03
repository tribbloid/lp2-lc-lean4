import Mathlib.Tactic
import «Lp2lc».Active.Shared

/-!
This file proves soundness for simply typed lambda calculus by interpreting
terms with a step-indexed logical relation. The step index is the fuel used to
reason about functions recursively: a function is safe for `steps` when, for
any `smaller_steps ≤ steps`, it sends semantically safe inputs to outputs that
stay safe one guarded step later.

The docstrings use tiny Scala-style STLC phrases as demonstrations. They only
use variables, lambdas, and application, and they reuse names such as `x`,
`f`, and `a` that also appear in the Lean definitions below.

```scala
f => x => f(x)
```
-/

namespace Lp2lc.Active.STLC.SI

structure Later (step : Prop) : Prop where
  force : step

inductive Ty : Type
| base : Ty
| arrow : (input : Ty) → (output : Ty) → Ty
deriving DecidableEq, Repr

namespace TypeNotation

scoped infixr:60 " :=> " => Ty.arrow

end TypeNotation

section

open scoped TypeNotation

inductive Term : Ty -> Type where
| term_variable : Var -> Term type
| unit : Term Ty.base
| lambda : Var -> Term output -> Term (input :=> output)
| apply : Term (input :=> output) -> Term input -> Term output

end

abbrev Env := List (Var × Ty)

open scoped TypeNotation

namespace Env

/--
Looks up the type associated with `name` in an environment.
The search proceeds from the front of the list, so a newer binder shadows an
older one. That matches the way nested lambda binders are read in STLC. E.g.

```scala
x => {x => x /* first "x" is shadowed*/}
```
-/
def get (name : Var) : Env → Option Ty
| [] => none
| (bound_name, type) :: env =>
    if name = bound_name then
      some type
    else
      get name env

end Env


/--
True if every free variable occurrence in `term` is typed in `env`:

- variable case: checks `env.get`
- lambda: checks its `body` under an extended environment that includes input variable, e.g.

  ```scala
  val z = 1
  {x : Int => x + z /* environment here is extended to include x */}
  ```

- application: requires both `f` and `a` to be scoped.
-/
def IsScoped (env : Env) {type : Ty}: (term: Term type) → Prop
| .term_variable x => env.get x = some type
| .unit => True
| @Term.lambda _ input x body => IsScoped ((x, input) :: env) body
| @Term.apply _ _ f a => IsScoped env f ∧ IsScoped env a

abbrev ScopedTerm (env : Env) (type : Ty) := { term : Term type // IsScoped env term }

/--
Convert each `Ty` into a lean semantic type.

(technically `Ty` can be coverted into anything, `PUnit` and lean functions are for convenience)
-/
def Denotation : (type : Ty) → Type
| .base => PUnit
| (input :=> output) => Denotation input → Denotation output

/--
Denotation lookup function type, given a value binded to variable name `name` in `env`, return its `Denotation`. E.g.

```scala
val f = {x: Int => x + 1}
```

in the above environment, if name-type pair `f: (Int => Int)` is given, then `Valuation env f (Int => Int) = Unit -> Uint`.
-/
abbrev Valuation (env : Env): Type := ∀ (name : Var) (type : Ty), env.get name = some type → Denotation type

/--
add a `name`-`value` pair into an existing `Valuation`. E.g.

```scala
// env0
var x = 1
// env1
x = x + 1

{ x =>
  // env2
  ???
}
```

both extension env0 -> env1 and env1 -> env2 cause the old name "x" to be shadowed
-/
def extend (valuation : Valuation env) (name : Var) (value : Denotation input) :
    Valuation ((name, input) :: env)
| tested_name, type, binding =>
    if same_name : tested_name = name then
      by
        subst same_name
        simp [Env.get] at binding
        cases binding
        exact value
    else
      valuation tested_name type (by simpa [Env.get, same_name] using binding)


private def denote_core (term : Term type) (hscoped : IsScoped env term) :
    Valuation env → Denotation type :=
  match term with
  | .term_variable name => fun valuation => valuation name _ hscoped
  | .unit => fun _ => PUnit.unit
  | @Term.lambda output input name body => fun valuation => fun (value : Denotation input) =>
      let body_scoped : IsScoped ((name, input) :: env) body := by
        simpa [IsScoped] using hscoped
      denote_core body body_scoped (extend valuation name value)
  | @Term.apply input output function argument => fun valuation =>
      (denote_core function hscoped.left valuation) (denote_core argument hscoped.right valuation)


/--
Evaluates a scoped term under a valuation into its semantic denotation.
Variables are read from the valuation, lambdas become Lean functions, and
applications are interpreted by semantic function application.

```scala
(x => x)(a)
```

`denote` interprets this by turning `x => x` into the identity function and then
applying it to the meaning of `a`.
-/
def denoteScoped (scopedTerm : ScopedTerm env type) :
    Valuation env → Denotation type :=
  denote_core scopedTerm.1 scopedTerm.2

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
-/
def Semantics : (type : Ty) → (steps : Nat) → Denotation type → Prop
| .base, _, _ => True
| (input :=> output), steps, function =>
    ∀ smaller_steps, smaller_steps ≤ steps →
      ∀ value, Semantics input smaller_steps value →
        Later (Semantics output smaller_steps (function value))

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
lemma Semantics.monotone {type : Ty} {smaller_steps steps : Nat} {value : Denotation type}
    (bound : smaller_steps ≤ steps) :
    Semantics type steps value → Semantics type smaller_steps value := by
  induction type generalizing smaller_steps steps with
  | base =>
      intro _
      trivial
  | arrow input output _ _ =>
      intro function_semantics test_steps test_bound test_value test_semantics
      exact function_semantics test_steps (le_trans test_bound bound) test_value test_semantics

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
def EnvironmentSemantics (env : Env) (steps : Nat) (valuation : Valuation env) : Prop :=
  ∀ (name : Var) (type : Ty) (binding : env.get name = some type),
    Semantics type steps (valuation name type binding)

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
    {env : Env} {smaller_steps steps : Nat} {valuation : Valuation env}
    (bound : smaller_steps ≤ steps) :
    EnvironmentSemantics env steps valuation → EnvironmentSemantics env smaller_steps valuation := by
  intro valuation_semantics name type binding
  exact Semantics.monotone bound (valuation_semantics name type binding)

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
lemma extend_semantics {env : Env} {input : Ty} {steps : Nat} {valuation : Valuation env}
    (valuation_semantics : EnvironmentSemantics env steps valuation)
    {name : Var} {value : Denotation input} (value_semantics : Semantics input steps value) :
    EnvironmentSemantics ((name, input) :: env) steps (extend valuation name value) := by
  intro tested_name type binding
  by_cases same_name : tested_name = name
  · subst same_name
    simp [extend, Env.get] at binding ⊢
    cases binding
    simpa [extend, Env.get] using value_semantics
  · have tail_binding : env.get tested_name = some type := by
      simpa [Env.get, same_name] using binding
    simpa [extend, same_name] using valuation_semantics tested_name type tail_binding

/--
The empty environment admits the unique valuation, since no variable can be
looked up. This is exactly what closed terms need: there are no free variables
whose meanings must be supplied externally.

```scala
x => x
```

The function above is closed because its only variable is bound by the lambda.
So `empty_valuation` never has to return a meaning for a genuinely free name.
-/
def empty_valuation : Valuation [] := by
  intro name type binding
  simp [Env.get] at binding


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
theorem fundamental {env : Env} {type : Ty} (term : ScopedTerm env type) :
    ∀ {steps : Nat} {valuation : Valuation env},
      EnvironmentSemantics env steps valuation →
      Semantics type steps (denoteScoped term valuation) := by
  rcases term with ⟨term, hscoped⟩
  induction term generalizing env with
  | term_variable name =>
      intro _ valuation valuation_semantics
      simpa [denoteScoped, denote_core] using valuation_semantics name _ hscoped
  | unit =>
      intro _ _ _
      trivial
  | @lambda output input name body induction_hypothesis =>
      intro steps valuation valuation_semantics smaller_steps smaller_bound value value_semantics
      have body_scoped : IsScoped ((name, input) :: env) body := by
        simpa [IsScoped] using hscoped
      exact ⟨induction_hypothesis (env := (name, input) :: env) (steps := smaller_steps)
        (valuation := extend valuation name value) body_scoped
        (extend_semantics (EnvironmentSemantics.monotone smaller_bound valuation_semantics) value_semantics)⟩
  | @apply input output function argument function_induction argument_induction =>
      intro steps valuation valuation_semantics
      exact (function_induction (valuation := valuation) hscoped.left valuation_semantics steps le_rfl
        (denoteScoped ⟨argument, hscoped.right⟩ valuation)
        (argument_induction (valuation := valuation) hscoped.right valuation_semantics)).force

abbrev closed (type : Ty) := ScopedTerm [] type

/--
A closed term is semantically sound in the empty environment at every step index.
This packages the fundamental theorem for programs without free variables, so no
external assumptions remain.

```scala
x => x
```

Because this term is closed, it is semantically valid under the empty valuation
for any number of steps. No external lookup is needed, since the only `x` is
bound inside the term itself.
-/
theorem soundness {type : Ty} (term : closed type) :
    ∀ steps, Semantics type steps (denoteScoped term empty_valuation) := by
  intro steps
  exact fundamental term (valuation := empty_valuation) (by
    intro name inner_type binding
    simp [Env.get] at binding)

end Lp2lc.Active.STLC.SI
