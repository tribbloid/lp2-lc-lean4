namespace Lp2lc.Active

namespace LC

inductive Typ (F: Type) : Type
| all : Typ F
deriving Repr

inductive Trm (F: Type) (G: Type) : Type
| bvar : Nat -> Trm F G
| fvar : String -> Trm F G -- Using String for simplicity
| abs : F -> G -> Trm F G
| app : G -> G -> Trm F G
deriving Repr

end LC

namespace STLC
end STLC

end Lp2lc.Active
