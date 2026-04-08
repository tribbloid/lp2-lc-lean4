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

def Instructions := String -- self-contained, concrete code with no variable or abstraction

inductive Ty : Type
| base : Ty
| arrow : (tyIn : Ty) → (tyOut : Ty) → Ty
deriving DecidableEq, Repr

scoped infixr:60 " :=> " => Ty.arrow

inductive Term : Type where
| term_variable : Var -> Term
| literal : Instructions -> Term
| lambda : Var -> Term -> Term
| apply : Term -> Term -> Term

def Env := List (Var × Ty)

namespace Env

@[simp] def empty : Env := []

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

inductive Checked : Env -> Term -> Ty -> Type where
| term_variable {env : Env} {name : Var} {type : Ty} :
    env.get name = some type ->
    Checked env (.term_variable name) type
| literal {env : Env} (code : Instructions) :
    Checked env (.literal code) Ty.base
| lambda {env : Env} {name : Var} {body : Term} {tyIn tyOut : Ty} :
    Checked ((name, tyIn) :: env) body tyOut ->
    Checked env (.lambda name body) (tyIn :=> tyOut)
| apply {env : Env} {function argument : Term} {tyIn tyOut : Ty} :
    Checked env function (tyIn :=> tyOut) ->
    Checked env argument tyIn ->
    Checked env (.apply function argument) tyOut

abbrev Typing (env : Env) (term : Term) (type : Ty) : Prop :=
  Nonempty (Checked env term type)

/--
True if `term` admits some extrinsic typing derivation in `env`.
-/
@[simp] def IsScoped (env : Env) (term : Term) : Prop := ∃ type, env.Typing term type

structure ScopedTerm (env : Env) (type : Ty) where
  term : Term
  checked : Checked env term type

end Env

/--
Convert each `Ty` into a Lean semantic data type.

(technically `Ty` can be coverted into anything, `String` and lean functions are for convenience)
-/
def Ty.Denotation : (type : Ty) → Type
| .base => Instructions
| (tyIn :=> tyOut) => tyIn.Denotation → tyOut.Denotation

/--
Bundles an environment together with a denotation lookup for its typed variable bindings. E.g.

```scala
val f = {x: Int => x + 1}
```

if `f : Int => Int` is in the environment, then `varLookup` returns its semantic
meaning as a Lean function.
-/
structure REPL where
  env: Env
  varLookup:  ∀ (name : Var) (type : Ty), (env.get name = some type) → Ty.Denotation type

namespace REPL

@[simp] def empty : REPL where
  env := []
  varLookup := fun _ _ binding => by
    cases binding

/--
Add a `name`-`value` pair into an existing REPL. E.g.

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
@[simp] def extend (repl : REPL) (name : Var)
    (value : Ty.Denotation input) : REPL where
  env := (name, input) :: repl.env
  varLookup := fun tested_name type binding =>
    if same_name : tested_name = name then
      by
        subst same_name
        simp at binding
        cases binding
        exact value
    else
      repl.varLookup tested_name type (by simpa [same_name] using binding)

/--
Evaluates a scoped term into its semantic denotation.

- variables in Env need no evaluation: they are directly from REPL lookup
- lambdas become semantic Lean functions composed from input variable and other existing variables in the REPL
- applications are interpreted by applying the semantic Lean function on the input term
-/
def eval (repl : REPL) (newTerm : repl.env.ScopedTerm type) : Ty.Denotation type :=

  let rec impl {type : Ty} {term : Term} (repl : REPL)
      (checked : Env.Checked repl.env term type) :
      Ty.Denotation type :=
    match checked with
    | .literal normal_form => normal_form
    | .term_variable binding => repl.varLookup _ _ binding
    | @Env.Checked.lambda _ name body input output body_checked =>
        fun (value : Ty.Denotation input) =>
        impl (repl.extend (input := input) name value) body_checked
    | @Env.Checked.apply _ function argument _ output function_checked argument_checked =>
        (impl repl function_checked) (impl repl argument_checked)

  impl repl newTerm.checked

end REPL

end STLC
