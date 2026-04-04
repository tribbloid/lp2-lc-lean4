import Mathlib.Tactic
import «Lp2lc».Active.Shared

/-!
This file proves soundness for simply typed lambda calculus by interpreting
terms with a step-indexed logical relation. The step index is the fuel used to
reason about functions recursively: a function is safe for `steps` when, for
any `smaller_steps ≤ steps`, it sends semantically safe inputs to outputs that
stay safe one guarded step later.

All docstrings use tiny Scala-style STLC phrases as demonstrations.
-/

namespace Lp2lc.Active.STLC

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
@[simp] def get (name : Var) : Env → Option Ty
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
@[simp] def IsScoped (env : Env) {type : Ty}: (term: Term type) → Prop
| .term_variable x => env.get x = some type
| .unit => True
| @Term.lambda _ input x body => IsScoped ((x, input) :: env) body
| @Term.apply _ _ f a => IsScoped env f ∧ IsScoped env a

def ScopedTerm (env : Env) (type : Ty) := { term : Term type // IsScoped env term }

/--
Convert each `Ty` into a Lean semantic type.

(technically `Ty` can be coverted into anything, `PUnit` and lean functions are for convenience)
-/
def Denotation : (type : Ty) → Type
| .base => PUnit
| (input :=> output) => Denotation input → Denotation output

/--
Bundles an environment together with a denotation lookup for its typed bindings. E.g.

```scala
val f = {x: Int => x + 1}
```

if `f : Int => Int` is in the environment, then `lookup` returns its semantic
meaning as a Lean function.
-/
structure Evaluator where
  env: Env
  lookup:  ∀ (name : Var) (type : Ty), (env.get name = some type) → Denotation type

namespace Evaluator

@[simp] def empty : Evaluator where
  env := []
  lookup := fun _ _ binding => by
    cases binding

/--
Add a `name`-`value` pair into an existing evaluator. E.g.

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
@[simp] def extend (evaluator : Evaluator) (name : Var) (value : Denotation input) : Evaluator where
  env := (name, input) :: evaluator.env
  lookup := fun tested_name type binding =>
    if same_name : tested_name = name then
      by
        subst same_name
        simp at binding
        cases binding
        exact value
    else
      evaluator.lookup tested_name type (by simpa [same_name] using binding)

/--
Given an evaluator, evaluates a scoped term into its semantic denotation.

- variables are read from the evaluator lookup
- lambdas become Lean functions
- applications are interpreted by semantic function application

-/
def denote (evaluator : Evaluator) (scopedTerm : ScopedTerm evaluator.env type) : Denotation type :=

  let rec impl {type : Ty} (evaluator : Evaluator) (term : Term type)
      (hscoped : IsScoped evaluator.env term) :
      Denotation type :=
    match term with
    | .unit => PUnit.unit
    | .term_variable name => evaluator.lookup name _ hscoped
    | @Term.lambda output input name body =>
        fun (value : Denotation input) =>
          let body_scoped : IsScoped ((name, input) :: evaluator.env) body := by
            simpa using hscoped
        impl (evaluator.extend (input := input) name value) body body_scoped
    | @Term.apply input output function argument =>
        (impl evaluator function hscoped.left) (impl evaluator argument hscoped.right)

  impl evaluator scopedTerm.1 scopedTerm.2

end Evaluator

end STLC
