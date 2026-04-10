import Mathlib.Tactic
import «Lp2lc».Active.Shared

/-!
This file defines simply typed lambda calculus and relevant compiler components, with the following conventions:

- higher-order syntax representation: the data structure representing term variables is unknown and
  irrelevant, all proof must be valid regardless of the concrete data structure.
  - this means that Variable name, de Bruijn serial are not a thing
  - Environment/Context should be indexed by the unknown term parameter
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

namespace Lp2lc.Active.STLC

structure Later (step : Prop) : Prop where
  force : step

def Instructions := String

section

variable (TermVar : Type) [DecidableEq TermVar]
variable (TypeVar : Type) [DecidableEq TypeVar] -- useless here

inductive Typ : Type
| base : Typ
| arrow : (tIn : Typ) → (tOut : Typ) → Typ
deriving DecidableEq, Repr

scoped infixr:60 " :=> " => Typ.arrow

inductive Trm : Type
| var : TermVar -> Trm
-- | literal : Instructions -> PreTerm TODO: remove, not in STLC
| function : (TermVar -> Trm) -> Trm
| apply : (function : Trm) -> (argument : Trm) -> Trm

namespace Semantic
-- In PHOAS syntax there is no Env data structure
-- The Lean interpreter local defs is term and type variable binding
-- The Lean evaluation of Prop is the heyting algebra of semantic typing and bound judgement

-- Type determines if a term can inhabits it, union & intersection type can be expressed easily
def Typ := Trm TermVar -> Prop

-- Bound determines if a type can fit somewhere into the subtyping hierarchy heyting algebra, not useful for STLC so far
-- bound is a (mostly implicit) term in Scala (`ev: T <:< Int`)
def Bound := Typ TermVar -> Prop

end Semantic

namespace Typ

def asSemantic: (self: Typ TermVar) -> Semantic.Typ TermVar :=
  sorry

end Typ

namespace Trm

def Denotation : (self : Trm TermVar) → Type :=
  sorry

end Trm

end section

end STLC
