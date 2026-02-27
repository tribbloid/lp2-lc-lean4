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

/-!
Sections below follow Coq file structure: Definitions → Substitution props →
Well-formedness lemmas → Weakening/Narrowing/Substitution → Regularity →
Preservation & Progress. Only statements are provided, proofs are `sorry`.
This file contains no axioms. All lemmas are unproven scaffolds.
-/

/-- Coq line ~267: preservation target packaged -/ 
theorem preservation_result : preservation := by
  -- TODO: port exact statement context if differs
  sorry

/-- Coq line ~272: progress target packaged -/
theorem progress_result : progress := by
  sorry

/- Substitution and opening properties -------------------------------------- -/

/-- Coq line ~406 (type-part): open_rec_lc_core for types -/
theorem open_rec_lc_core_T : ∀ (T : Typ) (j : Nat) (v u : Trm) (i : Nat),
  i ≠ j -> openTRec j v T = openTRec i u (openTRec j v T) -> T = openTRec i u T := by
  sorry

/-- Coq line ~406 (term-part): open_rec_lc_core for terms -/
theorem open_rec_lc_core_E : ∀ (e : Trm) (j : Nat) (v u : Trm) (i : Nat),
  i ≠ j -> openERec j v e = openERec i u (openERec j v e) -> e = openERec i u e := by
  sorry

/-- Coq line ~420 (type): open_rec_lc -/
theorem open_rec_lc_T : ∀ (T : Typ), LcT T -> ∀ u k, T = openTRec k u T := by
  sorry

/-- Coq line ~420 (term): open_rec_lc -/
theorem open_rec_lc_E : ∀ (e : Trm), LcE e -> ∀ u k, e = openERec k u e := by
  sorry

/-- Coq line ~429: opening a closed type with a var is identity -/
theorem open_t_var_type : ∀ (x : Var) (T : Typ), LcT T -> (T open_t_var x) = T := by
  sorry

/-- Coq line ~437: substitution for a fresh name is identity (types) -/
theorem subst_fresh_T : ∀ (T : Typ) (z : Var) (u : Trm), z ∉ fvT T -> substT z u T = T := by
  sorry

/-- Coq line ~437: substitution for a fresh name is identity (terms) -/ 
theorem subst_fresh_E : ∀ (e : Trm) (z : Var) (u : Trm), z ∉ fvE e -> substE z u e = e := by
  sorry

/-- Coq lines ~447-456: substitution distributes over open_rec (type/term) -/
theorem subst_open_rec_T : ∀ (T1 : Typ) (t2 : Trm) (x : Var) (u : Trm) (n : Nat),
  LcE u ->
  substT x u (openTRec n t2 T1) = openTRec n (substE x u t2) (substT x u T1) := by
  sorry

theorem subst_open_rec_E : ∀ (t1 t2 : Trm) (x : Var) (u : Trm) (n : Nat),
  LcE u ->
  substE x u (openERec n t2 t1) = openERec n (substE x u t2) (substE x u t1) := by
  sorry

/-- Coq line ~447: substitution distributes over open_t (type-side) -/
theorem substT_openT (T1 : Typ) (t2 : Trm) (x : Var) (u : Trm)
  (Hu : LcE u) :
  substT x u (openT T1 t2) = openT (substT x u T1) (substE x u t2) := by
  sorry

/-- Coq line ~447: substitution distributes over open_e (term-side) -/
theorem substE_openE (t1 t2 : Trm) (x : Var) (u : Trm)
  (Hu : LcE u) :
  substE x u (openE t1 t2) = openE (substE x u t1) (substE x u t2) := by
  sorry

/-- Coq line ~474: subst_t_open_t_var (types) -/
theorem substT_openT_var : ∀ (x y : Var) (u : Trm) (T : Typ), y ≠ x -> LcE u ->
  openT (substT x u T) (Trm.fvar y) = substT x u (openT T (Trm.fvar y)) := by
  sorry

/-- Coq line ~481: subst_e_open_e_var (terms) -/
theorem substE_openE_var : ∀ (x y : Var) (u : Trm) (e : Trm), y ≠ x -> LcE u ->
  openE (substE x u e) (Trm.fvar y) = substE x u (openE e (Trm.fvar y)) := by
  sorry

/-- Coq line ~491: subst_t_intro -/
theorem substT_intro : ∀ (x : Var) (T2 : Typ) (u : Trm), x ∉ fvT T2 -> LcE u ->
  openT T2 u = substT x u (T2 open_t_var x) := by
  sorry

/-- Coq line ~499: subst_e_intro -/
theorem substE_intro : ∀ (x : Var) (t2 : Trm) (u : Trm), x ∉ fvE t2 -> LcE u ->
  openE t2 u = substE x u (t2 open_e_var x) := by
  sorry

/-- Coq line ~509: substitutions preserve local closure (types) -/
theorem subst_lc_T : ∀ (T : Typ), LcT T -> ∀ z u, LcE u -> LcT (substT z u T) := by
  sorry

/-- Coq line ~509: substitutions preserve local closure (terms) -/
theorem subst_lc_E : ∀ (e : Trm), LcE e -> ∀ z u, LcE u -> LcE (substE z u e) := by
  sorry

/-- Coq line ~519: corollary (types) -/
theorem substT_type : ∀ (T : Typ) (z : Var) (u : Trm), LcT T -> LcE u -> LcT (substT z u T) := by
  intro T z u hT hu; exact subst_lc_T T hT z u hu

/-- Coq line ~525: corollary (terms) -/
theorem substE_term : ∀ (e1 : Trm) (z : Var) (e2 : Trm), LcE e1 -> LcE e2 -> LcE (substE z e2 e1) := by
  intro e1 z e2 he1 he2; exact subst_lc_E e1 he1 z e2 he2

/-- Coq line ~531: substitution preserves Value-hood -/
theorem substE_value : ∀ (e1 : Trm) (z : Var) (e2 : Trm), Value e1 -> LcE e2 -> Value (substE z e2 e1) := by
  sorry

/-- Coq line ~547: Value implies term -/
theorem value_is_term : ∀ (e : Trm), Value e -> LcE e := by
  sorry

/- Well-formedness and regularity ------------------------------------------ -/

/-- Coq line ~559: Wft implies local closure of types -/
theorem wft_lcT : ∀ {E T}, Wft E T -> LcT T := by
  intro E T _; sorry

/-- Coq line ~571: Wfe implies local closure of terms -/
theorem wfe_lcE : ∀ {E e}, Wfe E e -> LcE e := by
  intro E e _; sorry

/-- Coq line ~565: wft_type (alias) -/
theorem wft_type : ∀ {E T}, Wft E T -> LcT T := by
  intro E T h; exact (wft_lcT h)

/-- Coq line ~571: wfe_term (alias) -/
theorem wfe_term : ∀ {E e}, Wfe E e -> LcE e := by
  intro E e h; exact (wfe_lcE h)

/- Weakening / Narrowing / Substitution ------------------------------------ -/

/-- Coq line ~1102: sub_reflexivity -/
theorem sub_reflexivity : ∀ {E T}, Okt E -> Wft E T -> Sub E T T := by
  intro _ _ _ _; sorry
/-- Coq lines ~1116-1134: sub_has_weakening (packaged pair) -/ 
-- Ltac (Coq) reference: sub_has_mutind; apply_ih_bind; apply_fresh sub_all as Y; eauto
 theorem sub_has_weakening_pair :
  (∀ {E0 S T}, Sub E0 S T -> ∀ {E F G}, E0 = E ++ G -> Okt (E ++ F ++ G) -> Sub (E ++ F ++ G) S T)
  ∧ (∀ {E0 p T}, Has E0 p T -> ∀ {E F G}, E0 = E ++ G -> Okt (E ++ F ++ G) -> Has (E ++ F ++ G) p T) := by
  sorry

/-- Coq lines ~1116-1134: Sub weakening (packaged) -/ 
theorem sub_weakening : ∀ {E F G S T},
  Sub (E ++ G) S T -> Okt (E ++ F ++ G) -> Sub (E ++ F ++ G) S T := by
  intro _ _ _ _ _ _; sorry

/-- Coq lines ~1144-1157: sub_weakening1 -/
theorem sub_weakening1 : ∀ {E F G S T},
  Sub E S T -> Okt (E ++ F ++ G) -> Sub (E ++ F ++ G) S T := by
  intro _ _ _ _ _ _; sorry

/-- Coq lines ~1159-1172: sub_weakening_empty -/
theorem sub_weakening_empty : ∀ {E S T},
  Sub [] S T -> Okt E -> Sub E S T := by
  intro _ _ _ _; sorry

/-- Coq line ~1174: has_weakening -/
theorem has_weakening : ∀ {E F G p T},
  Has (E ++ G) p T -> Okt (E ++ F ++ G) -> Has (E ++ F ++ G) p T := by
  intro _ _ _ _ _ _; sorry

/-- Coq lines ~1182-1195: has_weakening1 -/
theorem has_weakening1 : ∀ {E F G p T},
  Has E p T -> Okt (E ++ F ++ G) -> Has (E ++ F ++ G) p T := by
  intro _ _ _ _ _ _; sorry

/-- Coq lines ~1197-1210: has_weakening_empty -/
theorem has_weakening_empty : ∀ {E p T},
  Has [] p T -> Okt E -> Has E p T := by
  intro _ _ _ _; sorry

/-- Coq lines ~1219–1248: sub_has_narrowing_aux (packaged)
Ltac (Coq) used here (for reference only):
- Hint Constructors Sub Has : core
- apply_fresh sub_all as Y; apply_ih_bind H0
- tests EQ: (x = z)
- lets M: (@okt_narrow Q)
- binds_middle_eq_inv; binds_cases
- has_sub; has_var; ok_from_okt; ok_middle_inv; sub_weakening1
- (proj2 wf_narrow)
-/
theorem sub_has_narrowing_aux :
  (∀ {E0 S T}, Sub E0 S T -> ∀ {Q E F z P}, E0 = (E ++ (z, Q) :: F) -> Sub E P Q -> Sub (E ++ (z, P) :: F) S T)
  ∧
  (∀ {E0 p T}, Has E0 p T -> ∀ {Q E F z P}, E0 = (E ++ (z, Q) :: F) -> Sub E P Q -> Has (E ++ (z, P) :: F) p T) := by
  sorry

/-- Coq line ~1219: sub_narrowing -/
theorem sub_narrowing : ∀ {Q E F Z P S T},
  Sub E P Q -> Sub (E ++ (Z, Q) :: F) S T -> Sub (E ++ (Z, P) :: F) S T := by
  intro _ _ _ _ _ _ _ _; sorry

/-- Coq lines ~1259-1269: sub_narrowing_empty -/
theorem sub_narrowing_empty : ∀ {Q Z P S T},
  Sub [] P Q -> Sub ((Z, Q) :: []) S T -> Sub ((Z, P) :: []) S T := by
  intro _ _ _ _ _; sorry

/-- Coq line ~1370: typing_weakening -/
theorem typing_weakening : ∀ {E F G e T},
  Typing (E ++ G) e T -> Okt (E ++ F ++ G) -> Typing (E ++ F ++ G) e T := by
  intro _ _ _ _ _ _ _; sorry

/-- Coq line ~1388: typing_narrowing -/
theorem typing_narrowing : ∀ {Q E F X P e T},
  Sub E P Q -> Typing (E ++ (X, Q) :: F) e T -> Typing (E ++ (X, P) :: F) e T := by
  intro _ _ _ _ _ _ _ _; sorry

/-- Coq lines ~1406-1416: typing_narrowing_empty -/
theorem typing_narrowing_empty : ∀ {Q X P e T},
  Sub [] P Q -> Typing ((X, Q) :: []) e T -> Typing ((X, P) :: []) e T := by
  intro _ _ _ _ _; sorry

-- Coq line ~1421: substitution for Typing -/
-- Ltac (Coq) reference: case_var; binds_get; apply_empty; concat_assoc_map_push; apply_fresh
theorem typing_through_subst : ∀ {U E F z T e u},
  Typing (E ++ (z,U) :: F) e T ->
  (Value u ∨ ∃ x, Trm.fvar x = u) -> Typing E u U ->
  Typing (E ++ mapSubst z u F) (substE z u e) (substT z u T) := by
  intro _ _ _ _ _ _ _ _ _ _; sorry

/- Environment and fv properties ------------------------------------------- -/

/- Free variables: opening and freshness ------------------------------------ -/
/-- Coq lines ~919-926: notin_fv_open_rec (type) -/
theorem notin_fv_open_rec_T : ∀ (T : Typ) (k : Nat) (y x : Var),
  x ∉ fvT (openTRec k (Trm.fvar y) T) -> x ∉ fvT T := by
  sorry

/-- Coq lines ~919-926: notin_fv_open_rec (term) -/
theorem notin_fv_open_rec_E : ∀ (e : Trm) (k : Nat) (y x : Var),
  x ∉ fvE (openERec k (Trm.fvar y) e) -> x ∉ fvE e := by
  sorry

/-- Coq lines ~929-934: notin_fv_t_open -/
theorem notin_fv_t_open : ∀ (y x : Var) (T : Typ),
  x ∉ fvT (openT T (Trm.fvar y)) -> x ∉ fvT T := by
  sorry

/-- Coq lines ~936-941: notin_fv_e_open -/
theorem notin_fv_e_open : ∀ (y x : Var) (e : Trm),
  x ∉ fvE (openE e (Trm.fvar y)) -> x ∉ fvE e := by
  sorry

/-- Coq lines ~943-953: notin_fv_wf_rec (type branch) -/
theorem notin_fv_wf_rec_T : ∀ {E : Env} {T : Typ},
  Wft E T -> ∀ x : Var, x ∉ Lp2lc.Active.Env.domOf E -> x ∉ fvT T := by
  sorry

/-- Coq lines ~943-953: notin_fv_wf_rec (term branch) -/
theorem notin_fv_wf_rec_E : ∀ {E : Env} {e : Trm},
  Wfe E e -> ∀ x : Var, x ∉ Lp2lc.Active.Env.domOf E -> x ∉ fvE e := by
  sorry

/-- Coq lines ~955-959: notin_fv_wf -/
theorem notin_fv_wf : ∀ {E : Env} {x : Var} {T : Typ},
  Wft E T -> x ∉ Lp2lc.Active.Env.domOf E -> x ∉ fvT T := by
  sorry

/-- Coq lines ~961-967: map_subst_id -/
theorem map_subst_id : ∀ {G : Env} {z : Var} {u : Trm},
  Okt G -> z ∉ Lp2lc.Active.Env.domOf G -> G = mapSubst z u G := by
  sorry

/- Well-formedness: weaken, narrow, substitute ------------------------------- -/
/-- Coq lines ~579-586, 600-606: wf_weaken (type/term) -/
theorem wf_weaken_T : ∀ {E F G : Env} {T : Typ},
  Wft (E ++ G) T -> ok (E ++ F ++ G) -> Wft (E ++ F ++ G) T := by
  sorry

/-- Term branch -/
theorem wf_weaken_E : ∀ {E F G : Env} {e : Trm},
  Wfe (E ++ G) e -> ok (E ++ F ++ G) -> Wfe (E ++ F ++ G) e := by
  sorry

/-- Coq lines ~587-596: wft_weaken -/
theorem wft_weaken : ∀ {E F G : Env} {T : Typ},
  Wft (E ++ G) T -> ok (E ++ F ++ G) -> Wft (E ++ F ++ G) T := by
  sorry

/-- Coq lines ~596-604: wft_weaken_empty -/
theorem wft_weaken_empty : ∀ {E : Env} {T : Typ},
  Wft [] T -> ok E -> Wft E T := by
  sorry

/-- Coq lines ~613-621: wfe_weaken -/
theorem wfe_weaken : ∀ {E F G : Env} {e : Trm},
  Wfe (E ++ G) e -> ok (E ++ F ++ G) -> Wfe (E ++ F ++ G) e := by
  sorry

/-- Coq lines ~626-638: wfe_weaken_empty -/
theorem wfe_weaken_empty : ∀ {e : Trm} {E : Env},
  Wfe [] e -> ok E -> Wfe E e := by
  sorry

/-- Coq lines ~642-660: wf_narrow (type branch) -/
theorem wf_narrow_T : ∀ {E0 : Env} {T : Typ},
  Wft E0 T -> ∀ {V F U E x}, E0 = (E ++ (x, V) :: F) -> ok (E ++ (x, U) :: F) -> Wft (E ++ (x, U) :: F) T := by
  sorry

/-- Coq lines ~647-660: wf_narrow (term branch) -/
theorem wf_narrow_E : ∀ {E0 : Env} {e : Trm},
  Wfe E0 e -> ∀ {V F U E x}, E0 = (E ++ (x, V) :: F) -> ok (E ++ (x, U) :: F) -> Wfe (E ++ (x, U) :: F) e := by
  sorry

/-- Coq lines ~662-668: wft_narrow -/
theorem wft_narrow : ∀ {V F U T E x},
  Wft (E ++ (x, V) :: F) T -> ok (E ++ (x, U) :: F) -> Wft (E ++ (x, U) :: F) T := by
  sorry

/-- Coq lines ~672-706: wf_subst (type branch) -/
theorem wf_subst_T : ∀ {E0 : Env} {T : Typ},
  Wft E0 T -> ∀ {F Q E Z u}, E0 = (E ++ (Z, Q) :: F) -> (Value u ∨ ∃ x, Trm.fvar x = u) -> Wfe E u -> ok (E ++ mapSubst Z u F) ->
  Wft (E ++ mapSubst Z u F) (substT Z u T) := by
  sorry

/-- Term branch -/
theorem wf_subst_E : ∀ {E0 : Env} {e : Trm},
  Wfe E0 e -> ∀ {F Q E Z u}, E0 = (E ++ (Z, Q) :: F) -> (Value u ∨ ∃ x, Trm.fvar x = u) -> Wfe E u -> ok (E ++ mapSubst Z u F) ->
  Wfe (E ++ mapSubst Z u F) (substE Z u e) := by
  sorry

/-- Coq lines ~708-715: wft_subst -/
theorem wft_subst : ∀ {F Q E Z u T},
  Wft (E ++ (Z, Q) :: F) T -> (Value u ∨ ∃ x, Trm.fvar x = u) -> Wfe E u -> ok (E ++ mapSubst Z u F) ->
  Wft (E ++ mapSubst Z u F) (substT Z u T) := by
  sorry

/-- Coq lines ~717-728: wft_subst1 -/
theorem wft_subst1 : ∀ {F Q Z u T},
  Wft ((Z, Q) :: F) T -> (Value u ∨ ∃ x, Trm.fvar x = u) -> Wfe [] u -> ok (mapSubst Z u F) ->
  Wft (mapSubst Z u F) (substT Z u T) := by
  sorry

/-- Coq lines ~730-742: wft_subst_empty -/
theorem wft_subst_empty : ∀ {Q Z u T},
  Wft ((Z, Q) :: []) T -> (Value u ∨ ∃ x, Trm.fvar x = u) -> Wfe [] u -> Wft [] (substT Z u T) := by
  sorry

/-- Coq line ~765: ok_from_okt -/ 
theorem ok_from_okt : ∀ {E : Env}, Okt E -> ok E := by
  intro _ _; sorry

/-- Coq line ~775: wft_from_env_has -/ 
theorem wft_from_env_has : ∀ {x U E}, Okt E -> bindsT x U E -> Wft E U := by
  intro _ _ _ _ _; sorry

/-- Coq lines ~818-824: okt_push_inv -/
theorem okt_push_inv : ∀ {E : Env} {x : Var} {T : Typ},
  Okt ((x, T) :: E) -> Okt E ∧ Wft E T ∧ x ∉ Lp2lc.Active.Env.domOf E := by
  sorry

/-- Coq lines ~826-832: okt_push_type -/
theorem okt_push_type : ∀ {E : Env} {x : Var} {T : Typ},
  Okt ((x, T) :: E) -> LcT T := by
  sorry

/-- Coq lines ~838-848: okt_narrow -/
theorem okt_narrow : ∀ {V U : Typ} {E F : Env} {x : Var},
  Okt (E ++ (x, V) :: F) -> Wft E U -> Okt (E ++ (x, U) :: F) := by
  sorry

/-- Coq lines ~852-894: okt_subst -/
theorem okt_subst : ∀ {Q : Typ} {Z : Var} {u : Trm} {E F : Env},
  Okt (E ++ (Z, Q) :: F) -> (Value u ∨ ∃ x, Trm.fvar x = u) -> Wfe E u -> Okt (E ++ mapSubst Z u F) := by
  sorry

/-- Coq lines ~896-904: okt_subst1 -/
theorem okt_subst1 : ∀ {Q : Typ} {Z : Var} {u : Trm} {F : Env},
  Okt ((Z, Q) :: F) -> (Value u ∨ ∃ x, Trm.fvar x = u) -> Wfe [] u -> Okt (mapSubst Z u F) := by
  sorry

/-- Coq line ~790: wft_from_okt -/ 
theorem wft_from_okt : ∀ {x T E}, Okt ((x,T)::E) -> Wft E T := by
  intro _ _ _ _; sorry

/-- Coq line ~800: wft_weaken_right -/ 
theorem wft_weaken_right : ∀ {T E F}, Wft E T -> ok (E ++ F) -> Wft (E ++ F) T := by
  intro _ _ _ _ _; sorry

/- Regularity of relations -------------------------------------------------- -/

/-- Coq lines ~975-987: sub_has_regular (Sub-branch) -/ 
theorem sub_regular : ∀ {E S T}, Sub E S T -> Okt E ∧ Wft E S ∧ Wft E T := by
  intro _ _ _ _; sorry

/-- Coq lines ~995-1006: has_regular and has_regular_e -/ 
theorem has_regular : ∀ {E p T}, Has E p T -> Okt E ∧ Wft E (Typ.sel p) ∧ Wft E T := by
  intro _ _ _ _; sorry

theorem has_regular_e : ∀ {E p T}, Has E p T -> (Value p ∨ ∃ x, Trm.fvar x = p) ∧ Wfe E p := by
  intro _ _ _ _; sorry

/-- Coq lines ~1489-1497: has_empty_value -/
theorem has_empty_value : ∀ {p T}, Has [] p T -> Value p := by
  intro _ _ _; sorry

/-- Coq lines ~1010-1031: typing_regular -/ 
theorem typing_regular : ∀ {E e T}, Typing E e T -> Okt E ∧ Wfe E e ∧ Wft E T := by
  intro _ _ _ _; sorry

/-- Coq line ~1035: value_regular -/ 
theorem value_regular : ∀ {t}, Value t -> LcE t := by
  intro _ _; sorry

/-- Coq line ~1043: red_regular -/ 
theorem red_regular : ∀ {t t'}, Red t t' -> LcE t ∧ LcE t' := by
  intro _ _ _; sorry

/- Additional wrappers ------------------------------------------------------ -/

/-- Coq line ~744: wft_open -/ 
theorem wft_open : ∀ {E u T1 T2}, ok E -> Wft E (Typ.all T1 T2) -> (Value u ∨ ∃ x, Trm.fvar x = u) -> Wfe E u -> Wft E (openT T2 u) := by
  intro _ _ _ _ _; sorry

/-- Coq line ~1276: has_value_var -/ 
 theorem has_value_var : ∀ {E u T}, Has E u T -> (Value u ∨ ∃ x, Trm.fvar x = u) := by
  sorry

/-- Coq line ~1286 etc.: sub_has_through_subst (packaged) -/ 
 theorem sub_has_through_subst : ∀ {E0 S T Q E F Z u},
  Sub E0 S T -> E0 = (E ++ (Z, Q) :: F) -> (Value u ∨ ∃ x, Trm.fvar x = u) -> Typing E u Q ->
  Sub (E ++ mapSubst Z u F) (substT Z u S) (substT Z u T) := by
  intro _ _ _ _ _ _ _ _ _ _ _; sorry

/-- Coq line ~1296: var_typing_has -/ 
theorem var_typing_has : ∀ {E x Q}, Typing E (Trm.fvar x) Q -> Has E (Trm.fvar x) Q := by
  intro _ _ _ _; sorry

/-- Coq line ~1296: val_typing_has -/ 
theorem val_typing_has : ∀ {E u Q}, Value u -> Typing E u Q -> Has E u Q := by
  intro _ _ _ _ _; sorry

/- Canonical forms and related results ------------------------------------- -/

/-- Coq lines ~1501-1511: psub_sub -/
theorem psub_sub : ∀ {S T}, PSub S T -> Sub [] S T := by
  intro _ _ _; sorry

/-- Coq lines ~1529-1541: possible_types_value/Wfe/Wft (first two here) -/
theorem possible_types_value : ∀ {n : Nat} {p : Trm} {T : Typ}, PossibleTypes n p T -> Value p := by
  intro _ _ _ _; sorry

theorem possible_types_wfe : ∀ {n : Nat} {p : Trm} {T : Typ}, PossibleTypes n p T -> Wfe [] p := by
  intro _ _ _ _; sorry

/-- Coq lines ~1556-1568: possible_types_wft -/
theorem possible_types_wft : ∀ {n : Nat} {p : Trm} {T : Typ}, PossibleTypes n p T -> Wft [] T := by
  intro _ _ _ _; sorry

/-- Coq lines ~1570-1581: has_empty_var_false -/
theorem has_empty_var_false : ∀ {x : Var} {T : Typ}, Has [] (Trm.fvar x) T -> False := by
  intro _ _ _; sorry

/-- Coq lines ~1583-1603: possible_types_closure_psub -/
theorem possible_types_closure_psub : ∀ {n : Nat} {v : Trm} {T U : Typ},
  PossibleTypes n v T -> PSub T U -> PossibleTypes n v U := by
  intro _ _ _ _ _; sorry

/-- Coq lines ~1605-1615: psub_reflexivity -/
theorem psub_reflexivity : ∀ {T : Typ}, Wft [] T -> PSub T T := by
  intro _ _; sorry

/-- Coq lines ~1617-1637: sub_psub_aux (split branches) -/
theorem sub_psub_aux_sub : ∀ {E : Env} {S T : Typ}, Sub E S T -> E = [] -> PSub S T := by
  intro _ _ _ _ _; sorry

theorem sub_psub_aux_has : ∀ {E : Env} {p : Trm} {T : Typ}, Has E p T -> E = [] -> PossibleTypes 0 p T := by
  intro _ _ _ _ _; sorry

/-- Coq lines ~1639-1643: sub_psub -/
theorem sub_psub : ∀ {S T : Typ}, Sub [] S T -> PSub S T := by
  intro _ _ _; sorry

/-- Coq lines ~1645-1652: possible_types_closure -/
theorem possible_types_closure : ∀ {n : Nat} {v : Trm} {T U : Typ},
  PossibleTypes n v T -> Sub [] T U -> PossibleTypes n v U := by
  intro _ _ _ _ _; sorry

/-- Coq lines ~1654-1673: possible_types_typing -/
theorem possible_types_typing : ∀ {v : Trm} {T : Typ}, Typing [] v T -> Value v -> PossibleTypes 1 v T := by
  intro _ _ _ _; sorry

/-- Coq lines ~1675-1690: typing_inv_abs -/
theorem typing_inv_abs : ∀ {S1 : Typ} {e1 : Trm} {T : Typ},
  Typing [] (Trm.abs S1 e1) T -> ∀ U1 U2, Sub [] T (Typ.all U1 U2) ->
  Sub [] U1 S1 ∧ ∃ S2 : Typ, ∃ L : Vars, ∀ x : Var, x ∉ L ->
    Typing ((x, S1) :: []) (openE e1 (Trm.fvar x)) (openT S2 (Trm.fvar x)) ∧ Sub ((x, U1) :: []) (openT S2 (Trm.fvar x)) (openT U2 (Trm.fvar x)) := by
  intro _ _ _ _ _ _; sorry

/-- Coq line ~1712: typing_through_subst1 -/ 
theorem typing_through_subst1 : ∀ {V y v e T}, Typing ((y,V)::[]) e T -> Value v -> Typing [] v V -> Typing [] (substE y v e) (substT y v T) := by
  intro _ _ _ _ _ _ _ _; sorry

/-- Coq line ~1729: value_red_contra -/ 
theorem value_red_contra : ∀ {e e'}, Value e -> Red e e' -> False := by
  intro _ _ _ _; sorry

/-- Coq line ~1695: canonical form for abs -/
theorem canonical_form_abs : ∀ {t U1 U2},
  Value t -> Typing [] t (Typ.all U1 U2) -> ∃ V e1, t = Trm.abs V e1 := by
  sorry

/-- Coq line ~1703: canonical form for mem -/
theorem canonical_form_mem : ∀ {t b T},
  Value t -> Typing [] t (Typ.mem b T) -> ∃ V, t = Trm.mem V := by
  sorry

end Lp2lc.Active.Dsubsup
