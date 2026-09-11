import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

structure Domain where
  P : Parameters
  V : Type
  adaptKVRefs {K V} (refs : KVRefs K (V : Sort u)) :
    refs.Adapter V
  adaptKVEquiv {K V refs} (equiv : KVEquiv (refs : KVRefs K (V : Sort u))) :
    equiv.Adapter (adaptKVRefs refs)

section variable (P : Parameters)

/-
FIXME: repair Src_, then migrate Trm.eval and Trm.infer into this file.

Requirements for the replacement:
- Certify a bundle of AST and KVEquiv P.C V: every AST.ref must be backed by
  an already-created or explicitly registered value, including captured references.
- Keep the same AST and PHOAS carrier P.C while expanding V as bindings require.
  kvEquiv.inv must remain total on each domain; Src_ must justify that domain.
- Evaluation uses Val: resolving an AST.ref must never fail with none.
- Inference expands the domain to Val ⊕ Typ: Val for free variables, Typ for
  bound variables whose values are not yet available.
- Keep all implementation in this file. Avoid duplicate syntax inductives and
  repeated traversal cases; aim for a simple compile-time/runtime logical relation.
- The migrated code, INCLUDING ALL new support, must NOT be longer than the
  original eval/infer implementation. Compressed formatting does not satisfy this.
- Commit the Src_ repair first, then evaluation and inference in separate commits.

Known WIP error: Src_.ast's expansion pattern currently has an extra argument.
-/

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
| void (ast : AST P label) : Src_ P label ⟨λ _ => PUnit.unit⟩
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
    (body : P.C → AST P .trm) (kvRefs2 : KVRefs P.C V2) : Src_ P .trm kvRefs2 --FIXME: remember kvRefs2 is an expansin of kvRef, it can be computed from adaptKVRefs, remove it

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
