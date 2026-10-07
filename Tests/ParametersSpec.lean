import «Lp2lc».Active.Parameters

namespace Tests.STLC.ParametersSpec

open Lp2lc.Active.Util
open Indices (FreeOrUnit)

section next

-- Rule: do not change order
private abbrev p0 : Parameters := { B := String, I := Indices.Serial, index := ⟨0⟩ }

example : p0.Next.index.down = 1 := rfl
example : p0.Next.Next.index.down = 2 := rfl
example : p0.Next.Next.Next.index.down = 3 := rfl
example : p0.Next.Next.Next.Next.index.down = 4 := rfl

#guard p0.Next.index.down = 1
#guard p0.Next.Next.index.down = 2
#guard p0.Next.Next.Next.index.down = 3
#guard p0.Next.Next.Next.Next.index.down = 4


example : FreeOrUnit.inc Empty = (Empty ⊕ Unit) := rfl
example : FreeOrUnit.inc (FreeOrUnit.inc Empty) = ((Empty ⊕ Unit) ⊕ Unit) := rfl
example : p0.Under p0.Next.Next := .lower (.lower .same)

end next

end Tests.STLC.ParametersSpec
