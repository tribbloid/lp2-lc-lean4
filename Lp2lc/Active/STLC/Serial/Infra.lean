import «Lp2lc».Active.STLC.Serial.Def

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

abbrev ValOrTyp := ExeValue ⊕ Typ -- Inference at a breakpoint accepts runtime values or types.

-- abbrev CompilerBindings := NatBindings ValOrTyp -- append-only
-- TODO: in STLC we assume that Typ can't bind free vars, this is not true in dependent type. Have to switch to the following in no time

structure CompilerValOrTyp : Type 2 where
  n : Nat
  value : (Val n) ⊕ (Typ n)
  captured : NatBindings CompilerValOrTyp

-- abbrev ExeBindings := NatBindings ExeValue -- append-only

end STLC
