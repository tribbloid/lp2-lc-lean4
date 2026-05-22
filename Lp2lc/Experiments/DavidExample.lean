

inductive Vec : Nat -> Type
| mk (n: Nat) (data: List Nat) : Vec n
deriving DecidableEq

def SameVecType : Prop := ∀ (x y : Nat) (_: x = y), (Vec x) = (Vec y)

def sameVecType : SameVecType := sorry

def vecTransport (x y : Nat) (eq: x = y) : Coe (Vec x) (Vec y) := sorry

def testVecTransport (a b : Nat) : Unit :=
  let v1 : Vec (a + b) := Vec.mk (a + b) List.empty
  let v2 : Vec (b + a) := v1
  .unit
