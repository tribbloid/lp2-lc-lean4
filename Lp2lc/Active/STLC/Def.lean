import Mathlib.Tactic
import «Lp2lc».Active.Shared

/-!
This file defines simply typed lambda calculus and relevant compiler components, with the following conventions:

- parametric higher-order abstract syntax (PHOAS) representation, namely:
  data structure representing term/type variables is unknown and
  irrelevant, all proof must be valid regardless of the chosen representation.
  - There is no variable name or de Bruijn serial.
  - There is no data structure representing Environment/Context variable bindings,
    they are just lean def/let bindings.
  - There is no class or data structure representing subtyping hierarchies,
    they are just bool/heyting algebra of lean Prop.
- extrinsic/Curry-style type representations: types of terms are predicates instead of built-in index.
- evaluation is a step-indexed logical relation. The step index is the fuel used to
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

namespace Lp2lc.Active.STLC

structure Later (step : Prop) : Prop where
  force : step

def Instructions := String

section PHOAS

variable (TermVar : Type) [DecidableEq TermVar]
variable (TypeVar : Type) [DecidableEq TypeVar] -- useless here

inductive Typ : Type
| base : Typ
| arrow : (tIn : Typ) → (tOut : Typ) → Typ
deriving DecidableEq, Repr

inductive Trm : Type
| var : TermVar -> Trm
-- | literal : Instructions -> PreTerm TODO: remove, not in core STLC
| function : (TermVar -> Trm) -> Trm
| apply : (function : Trm) -> (argument : Trm) -> Trm

scoped infixr:60 " :=> " => Typ.arrow

namespace Semantic

-- Type determines if a term can inhabits it, union & intersection type can be expressed easily
def Typ := Trm TermVar -> Prop

-- Bound determines if a type can fit somewhere into the subtyping hierarchy heyting algebra, not useful for STLC so far
-- bound is a (mostly implicit) term in Scala (`ev: T <:< Int`)
def Bound := Typ TermVar -> Prop

end Semantic

namespace Typ

-- how to convert a Typ into a semantic Typ judgement for terms
def asSemantic: (self: Typ) -> Semantic.Typ TermVar :=
  sorry

end Typ

namespace Trm

-- AKA Intermediate representation (IR): how to compute/beta-reduce the term in lean
def Denotation : (self : Trm TermVar) → Type :=
  sorry


end Trm

end PHOAS

end STLC
