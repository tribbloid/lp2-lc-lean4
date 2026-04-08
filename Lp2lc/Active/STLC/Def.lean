import Mathlib.Tactic
import «Lp2lc».Active.Shared

/-!
This file defines simply typed lambda calculus and relevant compiler components, with the following conventions:

- PHOAS syntax representation: the data structure representing both term and type variables are unknown and
  irrelevant, all proof must be valid regardless of the concrete data structure.
  - this means that Variable name, de Bruijn serial are not a thing
  - Environment/Context should be indexed by the unknown term/type parameter
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

def Instructions := String -- self-contained, concrete code/serialised data with no variable or abstraction

section
variable (TermVar TypeVar : Type)

inductive Ty : Type -- Pre-type
| base : Ty -- it is not need for syntax that includes System FSub, but keeping it won't hurt
| arrow : (tIn : TypeVar) → (tOut : TypeVar) → Ty
deriving DecidableEq, Repr

scoped infixr:60 " :=> " => Ty.arrow

inductive Tm : Type where -- Pre-term
  -- in PHOAS there is no bounded variable, variable also has no name or path
| freeVar : TypeVar -> Tm
| literal : Instructions -> Tm
  -- literally just a function in Lean that convert TypeVar to another Tern,
  -- in DOT this can be dependent function
| function : (TypeVar -> Tm) -> Tm
  -- apply the above function
| apply : (function: Tm) -> (argument: Tm) -> Tm

-- raw lookup from TermVar to pre-type declared by user
def Env := List (TermVar × Ty TypeVar)

-- Proof of inhabitance: true if `term: tT` in Scala compile successfully
-- def Typing := (term: Tm TermVar) -> (tT: Ty TypeVar) -> Prop


@[simp] def empty : Env TermVar TypeVar := []

end

namespace Env



end Env


end STLC
