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
-- | literal : Instructions -> PreTerm TODO: remove, not in core STLC
| function : ((argument : TrmVar) -> Trm) -> Trm
| apply : (function : Trm) -> (argument : Trm) -> Trm

scoped infixr:60 " :=> " => Typ.arrow

inductive HasType : Trm TrmVar -> Lp2lc.Active.STLC.Typ -> Prop where
| var {name : TrmVar} {declared : Lp2lc.Active.STLC.Typ} :
    HasType (.var name declared) declared
| function {body : TrmVar -> Trm TrmVar} {tIn tOut : Lp2lc.Active.STLC.Typ} :
    (∀ argument : TrmVar, HasType (body argument) tOut) ->
    HasType (.function body) (tIn :=> tOut)
| apply {function argument : Trm TrmVar} {tIn tOut : Lp2lc.Active.STLC.Typ} :
    HasType function (tIn :=> tOut) ->
    HasType argument tIn ->
    HasType (.apply function argument) tOut

namespace Semantic

-- A semantic type determines whether a term inhabits it; union and
-- intersection types can be expressed directly.
def Typ := Trm TrmVar -> Prop

-- A bound determines whether a type fits somewhere in the subtyping Heyting
-- algebra; this is not useful for core STLC so far.
-- bound is a (mostly implicit) term in Scala (`ev: T <:< Int`)
def Bound := Typ TrmVar -> Prop

end Semantic

namespace Typ

-- Convert a syntactic type into its semantic typing predicate on terms.
def asSemantic (self : Typ) : Semantic.Typ TrmVar :=
  fun term => HasType (TrmVar := TrmVar) term self

end Typ

namespace Trm

-- AKA intermediate representation (IR): reify the term in Lean.
-- map `_self` to a compatible lean type, e.g. Trm.function should be mapped to an actual lean function type
def Denotation (_self : Trm TrmVar) : Type := Trm TrmVar

-- AKA intermediate representation (IR): reify the term in Lean.
def denotation : (self : Trm TrmVar) -> self.Denotation :=
  fun self =>
    match self with
    | .var name declared => .var name declared
    | .function body => .function body
    | .apply fn arg => .apply (denotation fn) (denotation arg)


end Trm

end PHOAS

end STLC
