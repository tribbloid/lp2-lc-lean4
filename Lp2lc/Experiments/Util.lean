

import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

section

variable {Key : Type} {V : Type}

abbrev Lookup := Key → Option V

namespace Lookup

def empty : Lookup (Key := Key) (V := V) := λ _ => none

def set [DecidableEq Key] (σ : Lookup (Key := Key) (V := V)) (x : Key) (v : V) :
    Lookup (Key := Key) (V := V) :=
  λ y => if y = x then some v else σ y

@[simp] theorem set_same [DecidableEq Key] (σ : Lookup (Key := Key) (V := V)) (x : Key)
    (v : V) :
  set σ x v x = some v := by
  simp [set]

@[simp] theorem set_other [DecidableEq Key] (σ : Lookup (Key := Key) (V := V)) (x y : Key)
    (v : V) (h : y ≠ x) :
  set σ x v y = σ y := by
  simp [set, h]

end Lookup

end

end Util
