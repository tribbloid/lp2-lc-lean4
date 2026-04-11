import Mathlib.Tactic
import «Lp2lc».Active.Shared

/-!
This file defines the simply typed lambda calculus and related compiler
components, with the following conventions:

- parametric higher-order abstract syntax (PHOAS) representation, namely:
  the data structures representing term and type variables are abstract and
  irrelevant, so every proof must be valid regardless of the chosen
  representation.
  - There are no variable names or de Bruijn indices.
  - There is no data structure representing environment/context variable
    bindings; they are just Lean `def`/`let` bindings.
  - There is no class or data structure representing subtyping hierarchies;
    they are just the Heyting algebra of Lean `Prop`.
- extrinsic/Curry-style type representations: term types are predicates
  instead of built-in indices.
- evaluation is a step-indexed logical relation. The step index is the fuel used to
  reason about functions recursively: a function is safe for `steps` when, for
  any `smaller_steps < steps`, it sends semantically safe inputs to outputs that
  stay safe one guarded step later.

All docstrings use short Scala snippets (under 5 lines) as demonstrations.

Variable names follow these conventions:

- Lean variable for type, proposition and sort of any universe should use PascalCase (e.g. `Env`)
  - inductive cases should use camelCase (because they are constructors)
- Lean variable for terms, functions & data should use camelCase (e.g. `Env.bind`)
  - variable for DOT types, pre-types (which are Lean data) should start with `t` (e.g. tIn, tOut)
- use full name, not acronym or abbreviation
-/

namespace Lp2lc.Active.STLC

structure Later (step : Prop) : Prop where
  force : step

def Instructions := String

section PHOAS

variable (TrmVar : Type) [DecidableEq TrmVar]
variable (TypVar : Type) [DecidableEq TypVar] -- useless here

inductive Typ : Type
| base : Typ
| arrow : (tIn : Typ) → (tOut : Typ) → Typ
deriving DecidableEq, Repr

inductive Trm : Type
| var : TrmVar -> (declared: Typ) -> Trm
| literal : Instructions -> (declared: Typ) -> Trm -- not in core STLC, but included anyway to make it practical
| function : ((argument : TrmVar) -> Trm) -> Trm
| apply : (function : Trm) -> (argument : Trm) -> Trm

scoped infixr:60 " :=> " => Typ.arrow


namespace Semantic

-- semantic type is a generator of evidence that a term can inhabit it
-- union and intersection types can be expressed directly.
def Typ := Trm TrmVar -> Prop

-- A bound determines whether a type fits somewhere in the subtyping Heyting
-- algebra; this is not useful for core STLC so far.
-- bound is a (mostly implicit) term in Scala (`ev: T <:< Int`)
def Bound := Typ TrmVar -> Prop

end Semantic

namespace Typ

inductive AsSemantic : Typ -> Semantic.Typ TrmVar where
| var {name : TrmVar} {declared : Typ} :
    AsSemantic declared (.var name declared)
| literal {instructions : Instructions} {declared : Typ} :
    AsSemantic declared (.literal instructions declared)
| function {body : TrmVar -> Trm TrmVar} {tIn tOut : Typ} :
    (∀ argument : TrmVar, AsSemantic tOut (body argument)) ->
    AsSemantic (tIn :=> tOut) (.function body)
| apply {function argument : Trm TrmVar} {tIn tOut : Typ} :
    AsSemantic (tIn :=> tOut) function ->
    AsSemantic tIn argument ->
    AsSemantic tOut (.apply function argument)

end Typ

namespace Trm



end Trm

end PHOAS

end STLC
