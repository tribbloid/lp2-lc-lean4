import Mathlib.Data.List.AList
import «Lp2lc».Active.Shared

/-!
This file defines Hindley-Milner syntax and relevant compiler components, with the following conventions:

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

namespace Lp2lc.Active.HindleyMilner

structure Later (step : Prop) : Prop where
  force : step

def Instructions := String

section

variable {TypeVar : Type}
variable {TermVar : Type}

/--
Hindley-Milner monotypes.

```scala
Base
a => a
```
-/
inductive Ty : Type
| base : Ty
| var : TypeVar -> Ty
| arrow : (tIn : Ty) → (tOut : Ty) → Ty

local notation "ThisType" => Ty (TypeVar := TypeVar)

scoped infixr:60 " :=> " => Ty.arrow

/--
Hindley-Milner type schemes.

```scala
Base
[a] => a => a
```
-/
inductive Scheme : Type
| mono : ThisType -> Scheme
| poly : (fn : TypeVar → Scheme) -> Scheme

local notation "ThisScheme" => Scheme (TypeVar := TypeVar)

/--
Hindley-Milner terms use let-binding for implicit polymorphism.

```scala
let id = fun x => x in id id
```
-/
inductive Tm : Type
| var : TermVar -> Tm
| literal : Instructions -> Tm
| function : (fn : TermVar -> Tm) -> Tm
| apply : (function : Tm) -> (argument : Tm) -> Tm
| letBinding : (value : Tm) -> (body : TermVar -> Tm) -> Tm

structure Env where
  termBindings : AList (fun _ : TermVar => ThisScheme)
  typeBindings : AList (fun _ : TypeVar => Unit)

local notation "ThisEnv" => Env (TypeVar := TypeVar) (TermVar := TermVar)

namespace Env

@[simp] def empty : ThisEnv where
  termBindings := ∅
  typeBindings := ∅

@[simp] def extendTerm [DecidableEq TermVar] (env : ThisEnv) (name : TermVar)
    (scheme : ThisScheme) : ThisEnv where
  termBindings := env.termBindings.insert name scheme
  typeBindings := env.typeBindings

@[simp] def extendType [DecidableEq TypeVar] (env : ThisEnv) (name : TypeVar) : ThisEnv where
  termBindings := env.termBindings
  typeBindings := env.typeBindings.insert name ()

@[simp] def extend [DecidableEq TermVar] (env : ThisEnv) (name : TermVar)
    (scheme : ThisScheme) : ThisEnv :=
  env.extendTerm name scheme

@[simp] def getTerm [DecidableEq TermVar] (name : TermVar) (env : ThisEnv) : Option ThisScheme :=
  env.termBindings.lookup name

@[simp] def getType [DecidableEq TypeVar] (name : TypeVar) (env : ThisEnv) : Option Unit :=
  env.typeBindings.lookup name

end Env

end

end HindleyMilner
