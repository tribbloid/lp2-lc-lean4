import Std
import Mathlib.Data.Finset.Basic

namespace Lp2lc.Active

-- Shared variable type and finite set of variables
structure Var where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

abbrev Vars := Finset Var


-- Generic environment helpers over lists of (Var × α)
namespace Env
  /-- Domain (set of variables) of an environment represented as a list of (Var × α) -/
  def domOf {α} (E : List (Var × α)) : Vars := E.map (·.1) |>.toFinset

  /-- Membership predicate for bindings in an environment list -/
  def bindsOf {α} (x : Var) (v : α) (E : List (Var × α)) : Prop :=
    E.lookup x = some v

  def binds {α} (x : Var) (v : α) (E : List (Var × α)) : Prop :=
    E.lookup x = some v

  /-- Map a function over the second component of each binding -/
  def mapSecond {α β} (f : α → β) (E : List (Var × α)) : List (Var × β) :=
    E.map (fun p => (p.1, f p.2))

  def dom {α} (E : List (Var × α)) : Vars := E.map (·.1) |>.toFinset
end Env


-- Axiom: there is always a variable fresh from a finite set
axiom var_fresh : (L : Vars) → ∃ X : Var, X ∉ L

/-- Abstract well-formedness of environments.
This polymorphic axiom mirrors LibEnv.ok at the signature level.
Each module may instantiate `Env` as a List (Var × Bind) or similar. -/
axiom ok {Env : Sort u} : Env → Prop

end Lp2lc.Active


-----

inductive Which : Type -- only a tag/index for AST of different nature
| typ
| trm
deriving DecidableEq, Repr

def Rep := Which -> Type -- both types and terms are represented by a type family from `Which`
