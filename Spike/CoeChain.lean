structure Dim deriving DecidableEq

structure Vec (n : Dim)
deriving Repr, DecidableEq

theorem VecEq (d1 d2 : Dim) {h : d1 = d2} : Vec d1 = Vec d2 := congrArg Vec h

instance {d1 d2 : Dim} (v : Vec d1) (h : d1 = d2) : CoeDep (Vec d1) v (Vec d2) where
  coe := cast (by rw [h]) v
