namespace Tests.EquivIsoDemo

universe u v

def same_parity (m n : Nat) : Prop :=
  m % 2 = n % 2

theorem same_parity_equivalence : Equivalence same_parity := by
  constructor
  case refl =>
    intro n
    rfl
  case symm =>
    intro m n h
    exact h.symm
  case trans =>
    intro m n k hmn hnk
    exact hmn.trans hnk

example : same_parity 2 4 := by
  rfl

example : Not (same_parity 2 3) := by
  simp [same_parity]

structure TypeEquiv (A : Type u) (B : Type v) where
  to_fun : A -> B
  inv_fun : B -> A
  left_inv : forall a, inv_fun (to_fun a) = a
  right_inv : forall b, to_fun (inv_fun b) = b

structure TypeIso (A : Type u) (B : Type v) where
  hom : A -> B
  inv : B -> A
  inv_hom_id : forall a, inv (hom a) = a
  hom_inv_id : forall b, hom (inv b) = b

namespace TypeEquiv

def to_iso {A : Type u} {B : Type v} (e : TypeEquiv A B) : TypeIso A B where
  hom := e.to_fun
  inv := e.inv_fun
  inv_hom_id := e.left_inv
  hom_inv_id := e.right_inv

end TypeEquiv

namespace TypeIso

def to_type_equiv {A : Type u} {B : Type v} (i : TypeIso A B) : TypeEquiv A B where
  to_fun := i.hom
  inv_fun := i.inv
  left_inv := i.inv_hom_id
  right_inv := i.hom_inv_id

end TypeIso

def bool_with_unit_equiv : TypeEquiv Bool (Prod Bool Unit) where
  to_fun b := (b, ())
  inv_fun p := p.1
  left_inv := by
    intro b
    cases b <;> rfl
  right_inv := by
    intro p
    cases p with
    | mk b u =>
      cases u
      cases b <;> rfl

def bool_with_unit_iso : TypeIso Bool (Prod Bool Unit) :=
  bool_with_unit_equiv.to_iso

example : bool_with_unit_equiv.to_fun true = (true, ()) := by
  rfl

example : bool_with_unit_iso.inv (false, ()) = false := by
  rfl

example : bool_with_unit_iso.to_type_equiv.to_fun true = (true, ()) := by
  rfl

end Tests.EquivIsoDemo
