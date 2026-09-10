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
inductive Src_ (P : Parameters) : (label : Label) → {V : Type} → (kvRefs : KVRefs P.C V) → Type 1 where
/--
free var exist but devoid of information, `V := Unit`. (It's a special case of `assuming`)
-/
| void (ast : AST P label) : Src_ P label (KVRefs.unit P.C)
/--
in PHOAS convention `ast_` must be closed because `_P` can only be from the binder, TODO: unfortunately `ast_` won't have parametricity by default, attach predicate?
-/
| closed (ast_ : (_P : Parameters) → AST _P label) (kvRefs : KVRefs P.C V) : Src_ P label kvRefs
-- /--
-- given any `V`, free var either don't exist (closed AST), or exist but can always be mapped to `V`. Obviously this is cheating.
-- -/
-- | assuming (V : Sort u) (ast : AST P label) : Src_ label V
/--
Given an input Src_, a binder and a KVEquiv, applying the binder on the input can lead to an Src_ with expanded domain

The binder's input type `tIn` and the expanded domain `kvRefs2` are recorded so the underlying source term can be reassembled.
-/
| expansion {V1 V2 : Type} (tIn : AST P .typ) (arg : Src_ P .trm kvRefs1)
    (body : P.C → AST P .trm) (upcast : V1 ↪ V2) (kvRefs2 : KVRefs P.C V2) : Src_ P .trm kvRefs1 --FIXME: remember kvRefs2 is an expansin of kvRef, it can be comoputed from Parameters, remove it

namespace Src_

/--
Reassembles the plain source term from a certified spine, applying each binder back onto its input.
-/
def ast {label} {kvRefs : KVRefs P.C V} : (self : Src_ P label kvRefs) → AST P label
  | .void ast => ast
  | .closed _ast_ _kvRefs => _ast_ P
  | .expansion tIn arg body _upcast _kvRefs2 => .apply (.val (.lam body tIn)) arg.ast

end Src_

end


end STLC
