universe u

inductive UIdU where
  | mk

class UIdRefs (VK : UIdU → Sort u) where
  UId : UIdU
  get : (uid : UId) → VK UId

class UIdEquiv {VK} (base : UIdRefs VK) where
  inv : (value : VK base.UId) → base.UId

-- test 1: does dot notation already see through the `base` parameter?
#check (λ {base : UIdRefs (λ _ => Nat)} (e : UIdEquiv base) => e.UId)

-- test 2: with an explicit Coe instance
instance {VK} {base : UIdRefs VK} : Coe (UIdEquiv base) (UIdRefs VK) := ⟨base⟩

#check (λ {base : UIdRefs (λ _ => Nat)} (e : UIdEquiv base) => e.UId)

-- test 3: coe attribute on a wrapper function
def toView {VK} {base : UIdRefs VK} (_self : UIdEquiv base) : UIdRefs VK := base

attribute [coe] toView

#check (λ {base : UIdRefs (λ _ => Nat)} (e : UIdEquiv base) => e.UId)
