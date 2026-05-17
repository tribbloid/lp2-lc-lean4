namespace Tests.EquivIsoDemo

universe u v

structure TypeEquiv (A : Type u) (B : Type v) where
  toFun : A -> B
  invFun : B -> A
  leftInv : forall a, invFun (toFun a) = a
  rightInv : forall b, toFun (invFun b) = b

structure TypeIso (A : Type u) (B : Type v) where
  hom : A -> B
  inv : B -> A
  invHomId : forall a, inv (hom a) = a
  homInvId : forall b, hom (inv b) = b

namespace TypeEquiv

def toIso {A : Type u} {B : Type v} (e : TypeEquiv A B) : TypeIso A B where
  hom := e.toFun
  inv := e.invFun
  invHomId := e.leftInv
  homInvId := e.rightInv

end TypeEquiv

namespace TypeIso

def toTypeEquiv {A : Type u} {B : Type v} (i : TypeIso A B) : TypeEquiv A B where
  toFun := i.hom
  invFun := i.inv
  leftInv := i.invHomId
  rightInv := i.homInvId

end TypeIso

def boolWithUnitEquiv : TypeEquiv Bool (Prod Bool Unit) where
  toFun b := (b, ())
  invFun p := p.1
  leftInv := by
    intro b
    cases b <;> rfl
  rightInv := by
    intro p
    cases p with
    | mk b u =>
      cases u
      cases b <;> rfl

def boolWithUnitIso : TypeIso Bool (Prod Bool Unit) :=
  boolWithUnitEquiv.toIso

section boolWithUnit

example : boolWithUnitEquiv.toFun true = (true, ()) := by
  rfl

example : boolWithUnitIso.inv (false, ()) = false := by
  rfl

example : boolWithUnitIso.toTypeEquiv.toFun true = (true, ()) := by
  rfl

end boolWithUnit

end Tests.EquivIsoDemo
