import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

section variable (P : Parameters)

/--
Certified AST/KVEquiv bundle with every free variable guaranteed to be mapped to `V` (and vice versa)

The carrier type `P.C` never changes, but the domain type `V` can be expanded easily to include more data in `KVEquiv`.
A typical use case is to expand domain from `Val` only to `Val ⊕ Typ`, when compiling a term with free variables.

Critica component of our abstract rewriting system with reference binding.
-/
inductive Src_ (label : Label) {V} : (kvRefs : KVRefs P.C V) -> Type
/--
free var exist but devoid of information, `V := Unit`. (It's a special case of `assuming`)
-/
| void (ast: AST P label) : Src_ label KVRefs.ToUnit
/--
in PHOAS convention `ast_` must be closed because `_P` can only be from the binder, TODO: unfortunately `ast_` won't have parametricity by default, attach predicate?
-/
| closed (V: Sort u) (ast_ : (_P: Parameters) -> AST _P label) (kvRefs : KVRefs P.C V) : Src_ label kvRefs
-- /--
-- given any `V`, free var either don't exist (closed AST), or exist but can always be mapped to `V`. Obviously this is cheating.
-- -/
-- | assuming (V : Sort u) (ast : AST P label) : Src_ label V
/--
Given an input Src_, a binder and a KVEquiv, applying the binder on the input can lead to an Src_ with expanded domain
-/
| expansion {V1 V2} (arg: Src_ label r1) (body : P.C → AST P .trm) (upcast : V1 ↪ V2) : Src_ label (arg.kvEquiv.expand upcast)
with
  ast : AST P label V := sorry
  kvEquiv : KVEquiv P.C kvRefs := sorry

namespace Src_



end Src_

end


end STLC
