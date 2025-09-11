import «Lp2lc».Active.FsubL_alt.Def
import «Lp2lc».Active.FsubL_alt.Auxiliary

namespace Lp2lc.Active.FsubL_alt

open typ trm bind

-- Scaffolding: early substitution/opening lemmas (all sorry)
/-- Coq: open_tt_rec_type_core -/ 
@[simp] theorem open_tt_rec_type_core : ∀ T j V U i, i ≠ j →
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) →
  T = open_tt_rec i U T := by
  sorry

/-- Coq: open_tt_rec_type -/ 
@[simp] theorem open_tt_rec_type : ∀ T U, def_type T → ∀ k, T = open_tt_rec k U T := by
  sorry

/-- Coq: subst_tt_fresh -/ 
@[simp] theorem subst_tt_fresh : ∀ Z U T, Z ∉ fv_tt T → subst_tt Z U T = T := by
  sorry

/-- Coq: subst_tt_open_tt_rec -/ 
@[simp] theorem subst_tt_open_tt_rec : ∀ T1 T2 X P n, def_type P →
  subst_tt X P (open_tt_rec n T2 T1) = open_tt_rec n (subst_tt X P T2) (subst_tt X P T1) := by
  sorry

/-- Coq: subst_tt_open_tt -/ 
@[simp] theorem subst_tt_open_tt : ∀ T1 T2 X P, def_type P →
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2) := by
  sorry

/-- Coq: subst_tt_open_tt_var -/ 
@[simp] theorem subst_tt_open_tt_var : ∀ X Y U T, Y ≠ X → def_type U →
  open_tt (subst_tt X U T) (typ_fvar Y) = subst_tt X U (open_tt T (typ_fvar Y)) := by
  sorry

/-- Coq: subst_tt_intro -/ 
@[simp] theorem subst_tt_intro : ∀ X T2 U, X ∉ fv_tt T2 → def_type U →
  open_tt T2 U = subst_tt X U (open_tt T2 (typ_fvar X)) := by
  sorry

/-- Coq: open_te_rec_term_core -/ 
@[simp] theorem open_te_rec_term_core : ∀ e j u i P,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) → e = open_te_rec i P e := by
  sorry

/-- Coq: open_te_rec_type_core -/ 
@[simp] theorem open_te_rec_type_core : ∀ e j Q i P, i ≠ j →
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) → e = open_te_rec i P e := by
  sorry

/-- Coq: open_te_rec_term -/ 
@[simp] theorem open_te_rec_term : ∀ e U, def_term e → ∀ k, e = open_te_rec k U e := by
  sorry

/-- Coq: subst_te_fresh -/ 
@[simp] theorem subst_te_fresh : ∀ X U e, X ∉ fv_te e → subst_te X U e = e := by
  sorry

/-- Coq: subst_te_open_te -/ 
@[simp] theorem subst_te_open_te : ∀ e T X U, def_type U →
  subst_te X U (open_te e T) = open_te (subst_te X U e) (subst_tt X U T) := by
  sorry

/-- Coq: subst_te_open_te_var -/ 
@[simp] theorem subst_te_open_te_var : ∀ X Y U e, Y ≠ X → def_type U →
  open_te (subst_te X U e) (typ_fvar Y) = subst_te X U (open_te e (typ_fvar Y)) := by
  sorry

/-- Coq: subst_te_intro -/ 
@[simp] theorem subst_te_intro : ∀ X U e, X ∉ fv_te e → def_type U →
  open_te e U = subst_te X U (open_te e (typ_fvar X)) := by
  sorry

-- Term substitution
/-- Coq: open_ee_rec_term_core -/ 
@[simp] theorem open_ee_rec_term_core : ∀ e j v u i, i ≠ j →
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) → e = open_ee_rec i u e := by
  sorry

/-- Coq: open_ee_rec_type_core -/ 
@[simp] theorem open_ee_rec_type_core : ∀ e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) → e = open_ee_rec i u e := by
  sorry

/-- Coq: open_ee_rec_term -/ 
@[simp] theorem open_ee_rec_term : ∀ u e, def_term e → ∀ k, e = open_ee_rec k u e := by
  sorry

/-- Coq: subst_ee_fresh -/ 
@[simp] theorem subst_ee_fresh : ∀ x u e, x ∉ fv_ee e → subst_ee x u e = e := by
  sorry

/-- Coq: subst_ee_open_ee -/ 
@[simp] theorem subst_ee_open_ee : ∀ t1 t2 u x, def_term u →
  subst_ee x u (open_ee t1 t2) = open_ee (subst_ee x u t1) (subst_ee x u t2) := by
  sorry

/-- Coq: subst_ee_open_ee_var -/ 
@[simp] theorem subst_ee_open_ee_var : ∀ x y u e, y ≠ x → def_term u →
  open_ee (subst_ee x u e) (trm_fvar y) = subst_ee x u (open_ee e (trm_fvar y)) := by
  sorry

/-- Coq: subst_te_open_ee_var -/ 
@[simp] theorem subst_te_open_ee_var : ∀ Z P x e,
  open_ee (subst_te Z P e) (trm_fvar x) = subst_te Z P (open_ee e (trm_fvar x)) := by
  sorry

/-- Coq: subst_ee_open_te_var -/ 
@[simp] theorem subst_ee_open_te_var : ∀ z u e X, def_term u →
  open_te (subst_ee z u e) (typ_fvar X) = subst_ee z u (open_te e (typ_fvar X)) := by
  sorry

/-- Coq: subst_tt_type -/ 
@[simp] theorem subst_tt_type : ∀ T Z P, def_type T → def_type P → def_type (subst_tt Z P T) := by
  sorry

/-- Coq: subst_te_term -/ 
@[simp] theorem subst_te_term : ∀ e Z P, def_term e → def_type P → def_term (subst_te Z P e) := by
  sorry

/-- Coq: subst_ee_term -/ 
@[simp] theorem subst_ee_term : ∀ e1 Z e2, def_term e1 → def_term e2 → def_term (subst_ee Z e2 e1) := by
  sorry

end Lp2lc.Active.FsubL_alt
