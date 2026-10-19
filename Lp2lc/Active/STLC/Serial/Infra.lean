import «Lp2lc».Active.STLC.Serial.Def

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

abbrev ValOrTyp := ExeValue ⊕ Typ -- Inference at a breakpoint accepts runtime values or types.

-- abbrev CompilerBindings := NatBindings ValOrTyp -- append-only
-- TODO: use CompilerValOrTyp for compiler bindings so values and types retain their context and captured bindings.

structure CompilerValOrTyp : Type 2 where
  n : Nat
  value : (Val n) ⊕ (Typ n)
  captured : NatBindings CompilerValOrTyp

-- abbrev ExeBindings := NatBindings ExeValue -- append-only

end STLC
