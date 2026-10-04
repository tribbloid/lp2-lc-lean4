import «Lp2lc».Active.Parameters

namespace Tests.STLC.ParametersSpec

open Lp2lc.Active.Util

section next

-- Rule: do not change order
private def p0 : Parameters Indices.Serial := { B := String, index := 0 }

example : p0.Next.index = 1 := rfl
example : p0.Next.Next.index = 2 := rfl
example : p0.Next.Next.Next.index = 3 := rfl
example : p0.Next.Next.Next.Next.index = 4 := rfl

private def raw : Parameters Indices.Raw := { B := String, index := Empty }

example : raw.Next.index = (Empty ⊕ Unit) := rfl
example : raw.Next.Next.index = ((Empty ⊕ Unit) ⊕ Unit) := rfl
example : raw.Under raw.Next.Next := .lower (.lower .same)

end next

end Tests.STLC.ParametersSpec
