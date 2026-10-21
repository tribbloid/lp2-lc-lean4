import «Lp2lc».Active.Util

namespace Lp2lc.Active.Util

/-- Finite source-index bindings, newest entry first. -/
inductive NatBindings (α : Type 2) where
  | empty
  | set (self : NatBindings α) (index : Nat) (value : α)

namespace NatBindings

variable {α : Type 2}

def get (self : NatBindings α) (index : Nat) : Option α :=
  match self with
  | .empty => none
  | .set bindings key value => if key = index then some value else bindings.get index

instance : CoeFun (NatBindings α) (λ _ => Nat → Option α) := ⟨get⟩

end NatBindings

end Util
