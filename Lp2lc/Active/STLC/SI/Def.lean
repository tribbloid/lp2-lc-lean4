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

namespace Lp2lc.Active.STLC

namespace SI

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

def ScopedTerm (env : Env) (type : Ty) := { term : Term type // IsScoped env term }

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

in the above environment, if name-type pair `f: (Int => Int)` is given, then `Lookup env f (Int => Int) = Unit -> Uint`.
-/
def Env.Lookup (env : Env): Type := ∀ (name : Var) (type : Ty), env.get name = some type → Denotation type

/--
add a `name`-`value` pair into an existing Lookup. E.g.

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
def extend {env : Env} (lookup : env.Lookup) (name : Var) (value : Denotation input) :
    Env.Lookup ((name, input) :: env)
| tested_name, type, binding =>
    if same_name : tested_name = name then
      by
        subst same_name
        simp [Env.get] at binding
        cases binding
        exact value
    else
      lookup tested_name type (by simpa [Env.get, same_name] using binding)


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
def denote (scopedTerm : ScopedTerm env type) :
    env.Lookup → Denotation type :=

  let rec impl {env : Env} {type : Ty} (term : Term type) (hscoped : IsScoped env term) :
      env.Lookup → Denotation type :=
    match term with
    | .term_variable name => fun lookup => lookup name _ hscoped
    | .unit => fun _ => PUnit.unit
    | @Term.lambda output input name body => fun lookup => fun (value : Denotation input) =>
        let body_scoped : IsScoped ((name, input) :: env) body := by
          simpa [IsScoped] using hscoped
        impl body body_scoped (extend lookup name value)
    | @Term.apply input output function argument => fun lookup =>
        (impl function hscoped.left lookup) (impl argument hscoped.right lookup)

  impl scopedTerm.1 scopedTerm.2

end SI
