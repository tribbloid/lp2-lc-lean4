/-***************************************************************************
* DSubSup (D<:>) — Theorem statements scaffold                              *
* Coq source: Lp2lc_coq/Active/Dsubsup.v                                    *
* Rules:                                                                     *
* - Preserve names and declaration order; add TODO comments with Coq lines.  *
* - Proof bodies must remain `sorry` here; no axioms allowed.                *
***************************************************************************-/

import «Lp2lc».Active.Dsubsup.Def
import «Lp2lc».Active.Dsubsup.Auxiliary

namespace Lp2lc.Active.Dsubsup

open Trm Typ

/-!
Sections below follow Coq file structure: Definitions → Substitution props →
Well-formedness lemmas → Weakening/Narrowing/Substitution → Regularity →
Preservation & Progress. Only statements are provided, proofs are `sorry`.
-/

/-- Coq line ~267: preservation target packaged -/ 
theorem preservation_result : preservation := by
  -- TODO: port exact statement context if differs
  sorry

/-- Coq line ~272: progress target packaged -/
theorem progress_result : progress := by
  sorry

/- Substitution properties (selected statements mirrored) ------------------ -/

/-- Coq line ~447: subst distributes over open_t (typ-side) -/
theorem substT_openT (T1 : Typ) (t2 : Trm) (x : Var) (u : Trm)
  (Hu : LcE u) :
  substT x u (openT T1 t2) = openT (substT x u T1) (substE x u t2) := by
  sorry

/-- Coq line ~466: subst distributes over open_e (term-side) -/
theorem substE_openE (t1 t2 : Trm) (x : Var) (u : Trm)
  (Hu : LcE u) :
  substE x u (openE t1 t2) = openE (substE x u t1) (substE x u t2) := by
  sorry

/- Well-formedness and regularity ------------------------------------------ -/

/-- Coq line ~559: Wft implies local closure of types -/
theorem wft_lcT : ∀ {E T}, Wft E T -> LcT T := by
  intro E T h; induction h <;> try solve
    | simp
    | exact ?_;
  sorry

/-- Coq line ~571: Wfe implies local closure of terms -/
theorem wfe_lcE : ∀ {E e}, Wfe E e -> LcE e := by
  intro E e h; induction h <;> try solve
    | simp
    | exact ?_;
  sorry

/- Weakening / Narrowing / Substitution ------------------------------------ -/

/-- Coq line ~1136: weakening for Sub -/
theorem sub_weakening : ∀ {E F G S T},
  Sub (E ++ G) S T -> Okt (E ++ F ++ G) -> Sub (E ++ F ++ G) S T := by
  sorry

/-- Coq line ~1406: narrowing for Typing -/
theorem typing_narrowing : ∀ {Q E F X P e T},
  Sub E P Q -> Typing (E ++ (X,P) :: F) e T -> Typing (E ++ (X,Q) :: F) e T := by
  sorry

/-- Coq line ~1421: substitution for Typing -/
theorem typing_through_subst : ∀ {U E F z T e u},
  Typing (E ++ (z,U) :: F) e T ->
  (Value u ∨ ∃ x, Trm.fvar x = u) -> Typing E u U ->
  Typing (E ++ (List.map (fun (p : Var × Typ) => (p.1, p.2)) F)) (substE z u e) (substT z u T) := by
  -- NOTE: map is a placeholder mimic; env mapping for Typ is not required for statements here.
  sorry

/- Canonical forms (shapes) ------------------------------------------------ -/

/-- Coq line ~1695: canonical form for abs -/
theorem canonical_form_abs : ∀ {t U1 U2},
  Value t -> Typing [] t (Typ.all U1 U2) -> ∃ V e1, t = Trm.abs V e1 := by
  sorry

/-- Coq line ~1703: canonical form for mem -/
theorem canonical_form_mem : ∀ {t b T},
  Value t -> Typing [] t (Typ.mem b T) -> ∃ V, t = Trm.mem V := by
  sorry

end Lp2lc.Active.Dsubsup
