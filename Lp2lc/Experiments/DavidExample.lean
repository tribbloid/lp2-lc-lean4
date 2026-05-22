
set_option synthInstance.checkSynthOrder false


inductive Vec : Nat -> Type
| mk (n: Nat) (data: List Nat) : Vec n
deriving DecidableEq

instance vecTransport {x y : Nat} {ev: x = y} : Coe (Vec x) (Vec y) where
  coe v := cast (congrArg Vec ev) v

def testVecTransport (a b : Nat) : Unit :=
  let v1 : Vec (a + b) := Vec.mk (a + b) []
  let _v2 : Vec (b + a) := v1
  let _v2Hell : Vec (b + a) := (vecTransport (ev := Nat.add_comm a b)).coe v1
  .unit
