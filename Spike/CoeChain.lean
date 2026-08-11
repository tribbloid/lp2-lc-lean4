structure Dim deriving DecidableEq

structure Vec (n : Dim)
deriving Repr, DecidableEq

theorem VecEq (d1 d2 : Dim) {h : d1 = d2} : Vec d1 = Vec d2 := congrArg Vec h

def vecCoeDep {d1 d2 : Dim} (v : Vec d1) (h : d1 = d2) : CoeDep (Vec d1) v (Vec d2) where
  coe := cast (by rw [h]) v


def useVec (d : Dim)(x : Vec d): Nat := 1

section
    variable (d1 d2 : Dim)
    variable (v2 : Vec d2)
    variable (h : d1 = d2)

    def t := useVec d1 (cast (congrArg Vec h.symm) v2)
end
