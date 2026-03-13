import Std
import Mathlib.Data.Finset.Basic


namespace Lp2lc.Active

-- Shared variable type and finite set of variables
structure Var where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

abbrev Vars := Finset Var

namespace AnySys

mutual
-- variable (X: Type)

inductive Typ : Type
-- | _unknown: X -> Typ
| all : Typ
deriving Repr

-- Defining (pre)terms by recursion --
inductive Trm : Type
-- | _unknown: X -> TrmLike
| bvar : Nat → Trm
| fvar : Var → Trm
deriving Repr

end

-- class Sys (X: Type)
-- instance : Sys Typ where

end AnySys

-- Generic environment helpers over lists of (Var × α)
namespace Env
  /-- Domain (set of variables) of an environment represented as a list of (Var × α) -/
  def domOf {α} (E : List (Var × α)) : Vars := E.map (·.1) |>.toFinset

  /-- Membership predicate for bindings in an environment list -/
  def bindsOf {α} (x : Var) (v : α) (E : List (Var × α)) : Prop :=
    E.lookup x = some v

  /-- Map a function over the second component of each binding -/
  def mapSecond {α β} (f : α → β) (E : List (Var × α)) : List (Var × β) :=
    E.map (fun p => (p.1, f p.2))
end Env

-- Axiom: there is always a variable fresh from a finite set
axiom var_fresh : (L : Vars) → ∃ X : Var, X ∉ L

/-- Abstract well-formedness of environments.
This polymorphic axiom mirrors LibEnv.ok at the signature level.
Each module may instantiate `Env` as a List (Var × Bind) or similar. -/
axiom ok {Env : Sort u} : Env → Prop

end Lp2lc.Active


-----


namespace Exp

inductive TypLike (X: Type) : Type
| _unknown: X -> TypLike X
| all : TypLike X -- all-inclusive base type
| arrow : X -> X -> TypLike X
deriving Repr

end Exp
