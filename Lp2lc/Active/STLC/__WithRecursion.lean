import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

section variable (F : Free)

namespace AST.Rec

abbrev Typ := Lp2lc.Active.STLC.AST.Typ F

mutual

/--
Term syntax for STLC extended with recursive function values.

References remain the single binding form, so recursive calls are represented
by applying a referenced recursive function to an argument.
-/
inductive Trm : Type where
| val (value : Val)
| apply (fn : Trm) (arg : Trm)
| ref (ref : F.Carrier)

/--
Value syntax for STLC extended with recursive functions.

`recFn` binds the function's own reference before the argument reference in its
body. The output type annotation makes the recursive reference type available
to later typing rules.
-/
inductive Val : Type where
| primitive (repr : F.Data)
| fn (body : (arg : F.Carrier) -> Trm) (tIn : Typ F)
| recFn (body : (self : F.Carrier) -> (arg : F.Carrier) -> Trm) (tIn : Typ F) (tOut : Typ F)

end

end AST.Rec

end

end STLC

end Lp2lc.Active
