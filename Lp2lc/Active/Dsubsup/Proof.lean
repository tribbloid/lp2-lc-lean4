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

/-- Coq line ~406: open_rec_lc_core (scaffolded) -/
theorem open_rec_lc_core : True := by
  sorry

/-- Coq line ~420: open_rec_lc (scaffolded) -/
theorem open_rec_lc : True := by
  sorry

/-- Coq line ~429: open_t_var_type (scaffolded) -/
theorem open_t_var_type : True := by
  sorry

/-- Coq line ~437: subst_fresh (scaffolded) -/
theorem subst_fresh : True := by
  sorry

/-- Coq line ~447: subst distributes over open_t (typ-side) -/
theorem substT_openT (T1 : Typ) (t2 : Trm) (x : Var) (u : Trm)
  (Hu : LcE u) :
  substT x u (openT T1 t2) = openT (substT x u T1) (substE x u t2) := by
  sorry

/-- Coq line ~447: subst_open_rec (scaffolded, term-side) -/
theorem subst_open_rec : True := by
  sorry

/-- Coq line ~466: subst distributes over open_e (term-side) -/
theorem substE_openE (t1 t2 : Trm) (x : Var) (u : Trm)
  (Hu : LcE u) :
  substE x u (openE t1 t2) = openE (substE x u t1) (substE x u t2) := by
  sorry

/-- Coq line ~474: subst_t_open_t_var (scaffolded) -/
theorem substT_openT_var : True := by
  sorry

/-- Coq line ~481: subst_e_open_e_var (scaffolded) -/
theorem substE_openE_var : True := by
  sorry

/-- Coq line ~491: subst_t_intro (scaffolded) -/
theorem substT_intro : True := by
  sorry

/-- Coq line ~499: subst_e_intro (scaffolded) -/
theorem substE_intro : True := by
  sorry

/-- Coq line ~509: subst_lc (scaffolded) -/
theorem subst_lc : True := by
  sorry

/-- Coq line ~519: subst_t_type (scaffolded) -/
theorem substT_type : True := by
  sorry

/-- Coq line ~525: subst_e_term (scaffolded) -/
theorem substE_term : True := by
  sorry

/-- Coq line ~531: subst_e_value (scaffolded) -/
theorem substE_value : True := by
  sorry

/-- Coq line ~547: value_is_term (scaffolded) -/
theorem value_is_term' : True := by
  sorry

/- Well-formedness and regularity ------------------------------------------ -/

/-- Coq line ~559: Wft implies local closure of types (scaffolded) -/
theorem wft_lcT : ∀ {E T}, Wft E T -> LcT T := by
  intro E T _; sorry

/-- Coq line ~571: Wfe implies local closure of terms (scaffolded) -/
theorem wfe_lcE : ∀ {E e}, Wfe E e -> LcE e := by
  intro E e _; sorry

/-- Coq line ~565: wft_type (scaffolded) -/
theorem wft_type : ∀ {E T}, Wft E T -> LcT T := by
  intro E T h; exact (wft_lcT h)

/-- Coq line ~571: wfe_term (scaffolded) -/
theorem wfe_term : ∀ {E e}, Wfe E e -> LcE e := by
  intro E e h; exact (wfe_lcE h)

/- Weakening / Narrowing / Substitution ------------------------------------ -/

/-- Coq line ~1102: sub_reflexivity (scaffolded) -/
theorem sub_reflexivity : ∀ {E T}, Okt E -> Wft E T -> Sub E T T := by
  intro _ _ _ _; sorry

/-- Coq lines ~1116-1134: sub_has_weakening/weakening (scaffolded) -/
theorem sub_has_weakening : True := by
  sorry

theorem sub_weakening : ∀ {E F G S T},
  Sub (E ++ G) S T -> Okt (E ++ F ++ G) -> Sub (E ++ F ++ G) S T := by
  intro _ _ _ _ _ _; sorry

/-- Coq line ~1174: has_weakening (scaffolded) -/
theorem has_weakening : True := by
  sorry

/-- Coq line ~1219: sub_narrowing (scaffolded) -/
theorem sub_narrowing : True := by
  sorry

/-- Coq line ~1370: typing_weakening (scaffolded) -/
theorem typing_weakening : ∀ {E F G e T},
  Typing (E ++ G) e T -> Okt (E ++ F ++ G) -> Typing (E ++ F ++ G) e T := by
  intro _ _ _ _ _ _ _; sorry

/-- Coq line ~1388: typing_narrowing (scaffolded) -/
theorem typing_narrowing : ∀ {Q E F X P e T},
  Sub E P Q -> Typing (E ++ (X,P) :: F) e T -> Typing (E ++ (X,Q) :: F) e T := by
  intro _ _ _ _ _ _ _ _ _; sorry

-- Coq line ~1421: substitution for Typing (scaffolded) -/
theorem typing_through_subst : ∀ {U E F z T e u},
  Typing (E ++ (z,U) :: F) e T ->
  (Value u ∨ ∃ x, Trm.fvar x = u) -> Typing E u U ->
  Typing (E ++ F) (substE z u e) (substT z u T) := by
  intro _ _ _ _ _ _ _ _ _ _; sorry

/- Environment and fv properties (scaffolded) ------------------------------- -/

/-- Coq line ~765: ok_from_okt -/ 
theorem ok_from_okt : ∀ {E : Env}, Okt E -> ok E := by
  intro _ _; sorry

/-- wft_from_env_has (requires LibEnv binds) -/ 
theorem wft_from_env_has : True := by
  sorry

/-- Coq line ~790: wft_from_okt -/ 
theorem wft_from_okt : ∀ {x T E}, Okt ((x,T)::E) -> Wft E T := by
  intro _ _ _ _; sorry

/-- Coq line ~800: wft_weaken_right -/ 
theorem wft_weaken_right : True := by
  sorry

/-- Coq line ~818: okt_push_inv -/ 
theorem okt_push_inv : True := by
  sorry

/-- Coq line ~826: okt_push_type -/ 
theorem okt_push_type : True := by
  sorry

/-- Coq line ~838: okt_narrow -/ 
theorem okt_narrow : True := by
  sorry

/-- Coq line ~852: okt_subst -/ 
theorem okt_subst : True := by
  sorry

/-- Coq line ~896: notin_fv_open_rec -/ 
theorem notin_fv_open_rec : True := by
  sorry

/-- Coq line ~929: notin_fv_t_open -/ 
theorem notin_fv_t_open : True := by
  sorry

/-- Coq line ~936: notin_fv_e_open -/ 
theorem notin_fv_e_open : True := by
  sorry

/-- Coq line ~943: notin_fv_wf_rec -/ 
theorem notin_fv_wf_rec : True := by
  sorry

/-- Coq line ~955: notin_fv_wf -/ 
theorem notin_fv_wf : True := by
  sorry

/-- Coq line ~961: map_subst_id -/ 
theorem map_subst_id : True := by
  sorry

/- Regularity of relations (scaffolded) ------------------------------------- -/

/-- Coq lines ~975-987: sub_has_regular -/ 
theorem sub_regular : ∀ {E S T}, Sub E S T -> Okt E ∧ Wft E S ∧ Wft E T := by
  intro _ _ _ _; sorry

/-- Coq lines ~995-1006: has_regular and has_regular_e -/ 
theorem has_regular : ∀ {E p T}, Has E p T -> Okt E ∧ Wft E (Typ.sel p) ∧ Wft E T := by
  intro _ _ _ _; sorry

theorem has_regular_e : ∀ {E p T}, Has E p T -> (Value p ∨ ∃ x, Trm.fvar x = p) ∧ Wfe E p := by
  intro _ _ _ _; sorry

/-- Coq lines ~1010-1031: typing_regular -/ 
theorem typing_regular : ∀ {E e T}, Typing E e T -> Okt E ∧ Wfe E e ∧ Wft E T := by
  intro _ _ _ _; sorry

/-- Coq line ~1035: value_regular -/ 
theorem value_regular : ∀ {t}, Value t -> LcE t := by
  intro _ _; sorry

/-- Coq line ~1043: red_regular -/ 
theorem red_regular : ∀ {t t'}, Red t t' -> LcE t ∧ LcE t' := by
  intro _ _ _; sorry

/- Additional weakening and narrowing wrappers (scaffolded) ----------------- -/

theorem sub_weakening1 : True := by
  sorry

theorem sub_weakening_empty : True := by
  sorry

theorem has_weakening1 : True := by
  sorry

theorem has_weakening_empty : True := by
  sorry

theorem sub_narrowing_empty : True := by
  sorry

theorem typing_narrowing_empty : True := by
  sorry

/-- Coq line ~744: wft_open -/ 
theorem wft_open : ∀ {E u T1 T2}, ok E -> Wft E (Typ.all T1 T2) -> (Value u ∨ ∃ x, Trm.fvar x = u) -> Wfe E u -> Wft E (openT T2 u) := by
  intro _ _ _ _ _; sorry

/-- Coq line ~1286 etc.: sub_has_through_subst -/ 
theorem sub_has_through_subst : True := by
  sorry

/-- Coq line ~1296: var_typing_has -/ 
theorem var_typing_has : ∀ {E x Q}, Typing E (Trm.fvar x) Q -> Has E (Trm.fvar x) Q := by
  intro _ _ _ _; sorry

/-- Coq line ~1296: val_typing_has -/ 
theorem val_typing_has : ∀ {E u Q}, Value u -> Typing E u Q -> Has E u Q := by
  intro _ _ _ _ _; sorry

/- Canonical forms, inversion, and meta-results (scaffolded) ---------------- -/

/-- Coq line ~1712: typing_through_subst1 -/ 
theorem typing_through_subst1 : ∀ {V y v e T}, Typing ((y,V)::[]) e T -> Value v -> Typing [] v V -> Typing [] (substE y v e) (substT y v T) := by
  intro _ _ _ _ _ _ _ _; sorry

/-- Coq line ~1729: value_red_contra -/ 
theorem value_red_contra : ∀ {e e'}, Value e -> Red e e' -> False := by
  intro _ _ _ _; sorry

/-- Coq line ~1675 and ~1694: possible_types and psub related lemmas -/ 
theorem has_empty_value : True := by
  sorry

theorem psub_sub : True := by
  sorry

theorem possible_types_value : True := by
  sorry

theorem possible_types_wfe : True := by
  sorry

theorem possible_types_wft : True := by
  sorry

theorem has_empty_var_false : True := by
  sorry

theorem possible_types_closure_psub : True := by
  sorry

theorem psub_reflexivity : True := by
  sorry

theorem sub_psub_aux : True := by
  sorry

theorem sub_psub : True := by
  sorry

theorem possible_types_closure : True := by
  sorry

/-- Coq line ~1675 etc.: typing_inv_abs -/ 
theorem typing_inv_abs : True := by
  sorry

/- Remaining infrastructure lemmas from Coq (scaffolded as True) ------------- -/

theorem wf_weaken : True := by
  sorry

theorem wft_weaken : True := by
  sorry

theorem wft_weaken_empty : True := by
  sorry

theorem wfe_weaken : True := by
  sorry

theorem wfe_weaken_empty : True := by
  sorry

theorem wf_narrow : True := by
  sorry

theorem wft_narrow : True := by
  sorry

theorem wf_subst : True := by
  sorry

theorem wft_subst : True := by
  sorry

theorem wft_subst1 : True := by
  sorry

theorem wft_subst_empty : True := by
  sorry

theorem sub_has_narrowing_aux : True := by
  sorry

theorem possible_types_typing : True := by
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
