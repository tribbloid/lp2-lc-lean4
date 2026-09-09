import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

section variable (P : Parameters)

/--
Certified AST/KVRefs bundle with every free variable guaranteed to be mapped to `V`.

The carrier type `P.C` never changes, but the domain type `V` can be expanded easily to include more data in KVRefs

Critica component of our abstract rewriting system with reference binding.
-/
inductive Src_ (label : Label) : (V : Sort u) -> Type
/--
free var exist but devoid of information, `V := Unit`. (It's a special case of `assuming`)
-/
| void (ast: AST P label) : Src_ label PUnit
/--
in PHOAS convention `ast_` must be closed because `_P` can only be from the binder, TODO: unfortunately `ast_` won't have parametricity by default, attach predicate?
-/
| closed (V: Sort u) (ast_ : (_P: Parameters) -> AST _P label) : Src_ label V
-- /--
-- given any `V`, free var either don't exist (closed AST), or exist but can always be mapped to `V`. Obviously this is cheating.
-- -/
-- | assuming (V : Sort u) (ast : AST P label) : Src_ label V
/--
Given an input Src_, a binder and a KVEquiv, applying the binder on the input can lead to an Src_ with expanded domain
-/
| expansion {V1 V2} (arg: Src_ label V1) (body : P.C → AST P .trm) [equiv: KVEquiv P.C refs] (upcast : V1 ↪ V2) : Src_ label V2
with
  ast : AST P label := sorry
  refs : KVRefs P.C V := sorry

namespace Src_
section variable {V label} (this: Src_ P V label)


end
end Src_

end

namespace Domain
section variable {K V_} (this: Domain V_)

abbrev Src (label: Label) := Src_ this.refs label -- refs is empty, can expand to any direction

abbrev Typ := this.Src .typ
abbrev Trm := this.Src .trm
abbrev Val := this.Src .val


end
end Domain

abbrev Runtime (D: DataU) := Domain (λ K => -- value references: this include
  let P : Parameters := { C := K, D := D }
  AST.Val P
)

end STLC
