import Mathlib.Data.List.AList
import «Lp2lc».Active.Shared

/-!
This file defines System F and relevant compiler components, with the following conventions:

- higher-order syntax representation: the data structure representing type variables and term variables is unknown and
  irrelevant, all proof must be valid regardless of the concrete data structure.
  - this means that variable name, de Bruijn serial are not a thing
  - Environment/Context should be indexed by the unknown type and term parameters
- extrinsic/Curry-style type representations: types of terms are predicates instead of built-in index.
- interpretation is a step-indexed logical relation. The step index is the fuel used to
  reason about functions recursively: a function is safe for `steps` when, for
  any `smaller_steps < steps`, it sends semantically safe inputs to outputs that
  stay safe one guarded step later.

All docstrings use short (under 5 lines) of Scala code as demonstrations.

variable names always follow the following convention:

- Lean variable for type, proposition and sort of any universe should use PascalCase (e.g. `Env`)
  - inductive cases should use camelCase (because they are constructors)
- Lean variable for terms, functions & data should use camelCase (e.g. `Env.bind`)
  - variable for DOT types, pre-types (which are Lean data) should start with `t` (e.g. tIn, tOut)
- use full name, not acronym or abbreviation
-/

namespace Lp2lc.Active.SysF

structure Later (step : Prop) : Prop where
  force : step

def Instructions := String

section

variable {TypeVar : Type}
variable {TermVar : Type}

/--
System F types.

```scala
X => X
[X] => X => X
```
-/
inductive Ty : Type
| base : Ty
| var : TypeVar -> Ty
| arrow : (tIn : Ty) → (tOut : Ty) → Ty
| poly : (fn : TypeVar → Ty) → Ty

local notation "ThisType" => Ty (TypeVar := TypeVar)

scoped infixr:60 " :=> " => Ty.arrow

/--
System F terms with type abstraction and type application.

```scala
fun x => x
(id [Base]) value
```
-/
inductive Tm : Type
| var : TermVar -> Tm
| literal : Instructions -> Tm
| function : (fn : TermVar -> Tm) -> Tm
| apply : (function : Tm) -> (argument : Tm) -> Tm
| polyFunction : (fn : TypeVar -> Tm) -> Tm
| polyApply : (function : Tm) -> (argument : ThisType) -> Tm

structure Env where
  termBindings : AList (fun _ : TermVar => ThisType)
  typeBindings : AList (fun _ : TypeVar => Unit)

local notation "ThisEnv" => Env (TypeVar := TypeVar) (TermVar := TermVar)

namespace Env

@[simp] def empty : ThisEnv where
  termBindings := ∅
  typeBindings := ∅

@[simp] def extendTerm [DecidableEq TermVar] (env : ThisEnv) (name : TermVar)
    (type : ThisType) : ThisEnv where
  termBindings := env.termBindings.insert name type
  typeBindings := env.typeBindings

@[simp] def extendType [DecidableEq TypeVar] (env : ThisEnv) (name : TypeVar) : ThisEnv where
  termBindings := env.termBindings
  typeBindings := env.typeBindings.insert name ()

@[simp] def extend [DecidableEq TermVar] (env : ThisEnv) (name : TermVar)
    (type : ThisType) : ThisEnv :=
  env.extendTerm name type

@[simp] def getTerm [DecidableEq TermVar] (name : TermVar) (env : ThisEnv) : Option ThisType :=
  env.termBindings.lookup name

@[simp] def getType [DecidableEq TypeVar] (name : TypeVar) (env : ThisEnv) : Option Unit :=
  env.typeBindings.lookup name

end Env

end

end SysF
