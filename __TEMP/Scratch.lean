universe u

inductive UIdU where
  | mk

class UIdView (VK : UIdU → Sort u) where
  UId : UIdU
  get : (uid : UId) → VK UId

class UIdEquiv {VK} (base : UIdView VK) where
  inv : (value : VK base.UId) → base.UId

-- test 1: does dot notation already see through the `base` parameter?
#check (λ {base : UIdView (λ _ => Nat)} (e : UIdEquiv base) => e.UId)

-- test 2: with an explicit Coe instance
instance {VK} {base : UIdView VK} : Coe (UIdEquiv base) (UIdView VK) := ⟨base⟩

#check (λ {base : UIdView (λ _ => Nat)} (e : UIdEquiv base) => e.UId)

-- test 3: coe attribute on a wrapper function
def toView {VK} {base : UIdView VK} (_self : UIdEquiv base) : UIdView VK := base

attribute [coe] toView

#check (λ {base : UIdView (λ _ => Nat)} (e : UIdEquiv base) => e.UId)
