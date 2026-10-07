import «Lp2lc».Active.Util

namespace Lp2lc.Active.Util


/-- Finite source-index bindings, newest entry first. -/
structure Bindings (α : Type 1) where
  entries : List (Nat × α)

namespace Bindings

variable {α β : Type 1} (self : Bindings α)

def empty : Bindings α := ⟨[]⟩

instance : CoeFun (Bindings α) (λ _ => Nat → Option α) := ⟨λ self index => self.entries.lookup index⟩

def set (index : Nat) (value : α) : Bindings α := ⟨(index, value) :: self.entries⟩

def map (f : α → β) : Bindings β := ⟨self.entries.map (λ entry => (entry.1, f entry.2))⟩

@[simp] theorem getMap (f : α → β) (index : Nat) :
    self.map f index = (self index).map f := by
  rcases self with ⟨entries⟩
  induction entries <;> simp_all [map, List.lookup]
  split <;> simp_all

end Bindings

end Util
