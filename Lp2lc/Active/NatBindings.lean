import «Lp2lc».Active.Util

namespace Lp2lc.Active.Util


/-- Finite source-index bindings, newest entry first. -/
structure NatBindings (α : Type 2) where
  entries : List (Nat × α)

namespace NatBindings

variable {α β : Type 2} (self : NatBindings α)

def empty : NatBindings α := ⟨[]⟩

instance : CoeFun (NatBindings α) (λ _ => Nat → Option α) := ⟨λ self index => self.entries.lookup index⟩

def set (index : Nat) (value : α) : NatBindings α := ⟨(index, value) :: self.entries⟩

def map (f : α → β) : NatBindings β := ⟨self.entries.map (λ entry => (entry.1, f entry.2))⟩

@[simp] theorem getMap (f : α → β) (index : Nat) :
    self.map f index = (self index).map f := by
  rcases self with ⟨entries⟩
  induction entries <;> simp_all [map, List.lookup]
  split <;> simp_all

end NatBindings

end Util
