import «Lp2lc».Active.Parameters

namespace Tests.STLC.ParametersSpec

open Lp2lc.Active.Util

section next

-- Rule: do not change order
private abbrev p0 : Parameters := { B := String, I := Indices.Serial, index := 0 }

example : p0.Next.index = 1 := rfl
example : p0.Next.Next.index = 2 := rfl
example : p0.Next.Next.Next.index = 3 := rfl
example : p0.Next.Next.Next.Next.index = 4 := rfl

example : Indices.Raw.inc Empty = (Empty ⊕ Unit) := rfl
example : Indices.Raw.inc (Indices.Raw.inc Empty) = ((Empty ⊕ Unit) ⊕ Unit) := rfl
example : p0.Under p0.Next.Next := .lower (.lower .same)

end next

end Tests.STLC.ParametersSpec
