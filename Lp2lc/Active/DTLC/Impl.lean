import «Lp2lc».Active.DTLC.DTLCDef

namespace Lp2lc.Active

namespace DTLC

open Lp2lc.Active.Util

inductive Symbol where -- no constructor, it can only be retrieved from FBound

namespace Symbolic

@[reducible] def impl : Impl where
  I := Symbol
  B := String

abbrev ByteCode := impl.B
abbrev Typ := AST.Typ impl
abbrev Val := AST.Val impl
abbrev Trm := AST.Trm impl

end Symbolic

end DTLC

end Lp2lc.Active

-- namespace Trusted

-- def Spec (x y : Nat) : Prop :=
--   y = x + 1

-- unsafe def nextImpl (x : Nat) : Nat :=
--   if x < 1000000 then
--     x + 1
--   else
--     panic! "Trusted.next: runtime precondition violated"

-- @[implemented_by nextImpl]
-- opaque next (x : Nat) : Nat

-- axiom next_spec (x : Nat) : Spec x (next x)

-- theorem client_theorem (x : Nat):
--     next x = x + 1 := next_spec x

-- #eval next 41
-- -- compiled/evaluated code uses nextImpl

-- end Trusted
