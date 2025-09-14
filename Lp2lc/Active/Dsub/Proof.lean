/- Dsub Proof scaffolds

This file mirrors the lemmas in Coq Lp2lc_coq/Active/Dsub.v and provides theorem
statements with `sorry` placeholders. No axioms. Keep the original order.
-/

import Std
import «Lp2lc».Active.Dsub.Def
import «Lp2lc».Active.Dsub.Auxiliary

namespace Lp2lc.Active.Dsub

-- The proofs are extensive; here we set up a first batch of scaffolds. More will
-- be appended preserving Coq order and names (splitting /\ into suffix _t/_e
-- variants where needed).

-- Coq line 395: Lemma open_rec_lc_core (split into type/term halves)
-- Split naming: _t for types, _e for terms

theorem open_rec_lc_core_t : ∀ T j v u i,
  i ≠ j →
  open_t_rec j v T = open_t_rec i u (open_t_rec j v T) →
  T = open_t_rec i u T := by
  -- TODO: ported from Coq open_rec_lc_core (type part)
  sorry

theorem open_rec_lc_core_e : ∀ e j v u i,
  i ≠ j →
  open_e_rec j v e = open_e_rec i u (open_e_rec j v e) →
  e = open_e_rec i u e := by
  -- TODO: ported from Coq open_rec_lc_core (term part)
  sorry

-- Coq line 409: Lemma open_rec_lc (split)

theorem open_rec_lc_t : ∀ T,
  def_type T → ∀ u k, T = open_t_rec k u T := by
  -- TODO
  sorry

theorem open_rec_lc_e : ∀ e,
  def_term e → ∀ u k, e = open_e_rec k u e := by
  -- TODO
  sorry

-- Coq line 418: Lemma open_t_var_type

theorem open_t_var_type : ∀ x T,
  def_type T → open_t T (trm.trm_fvar x) = T := by
  -- TODO
  sorry

-- Coq lines 426-433: subst_fresh (split)

theorem subst_fresh_t : ∀ T z u,
  z ∉ fv_t T → subst_t z u T = T := by
  -- TODO
  sorry

theorem subst_fresh_e : ∀ e z u,
  z ∉ fv_e e → subst_e z u e = e := by
  -- TODO
  sorry

-- Coq lines 541–548: value_is_term

theorem value_is_term : ∀ e, value e -> def_term e := by
  -- TODO: Coq value_regular
  sorry

-- Coq lines 548–564: wf_lc split

theorem wf_lc_t : ∀ E T, wft E T -> def_type T := by
  -- TODO: Coq wf_lc (type part)
  sorry


theorem wf_lc_e : ∀ E e, wfe E e -> def_term e := by
  -- TODO: Coq wf_lc (term part)
  sorry

end Lp2lc.Active.Dsub
