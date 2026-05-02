def Index := Type 1

section Syntax
variable (I : Index)

inductive Trm : Index where
| var (symbol : I)
| val (v : Val)

inductive Val : Index where
| primitive (repr : String)
| depFn (body : (arg : I) -> Trm)
end Syntax

instance : Coe Type Index where
  coe := ULift

instance {α : Type} : Coe (ULift α) α where
  coe := ULift.down

def pretty (e : Trm String) : String :=
  match e with
  | Trm.var s => s
  | Trm.val n => toString n
