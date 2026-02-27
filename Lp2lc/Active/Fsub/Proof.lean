/-***************************************************************************
* Preservation and Progress for System-F with Subtyping - Proofs           *
***************************************************************************-/

import «Lp2lc».Active.Fsub.Def

namespace Lp2lc.Active.Fsub

open Typ Trm Bind

-- Properties of type substitution in type

-- Coq line 430: Lemma open_tt_rec_type_core
theorem open_tt_rec_type_core : ∀ T j V U i, i ≠ j →
  (open_tt_rec j V T) = open_tt_rec i U (open_tt_rec j V T) →
  T = open_tt_rec i U T := by
  intro T
  induction T with
  | typ_top =>
      intro j V U i _ _
      simp [open_tt_rec]
  | typ_bvar n =>
      intro j V U i hneq h
      by_cases hj : j = n
      · subst hj
        have hi : i ≠ j := hneq
        simp [open_tt_rec, hi]
      · by_cases hi : i = n
        · subst hi
          have hji : j ≠ i := by simpa [eq_comm] using hj
          simp [open_tt_rec, hji] at h ⊢
          exact h
        · simp [open_tt_rec, hi]
  | typ_fvar X =>
      intro j V U i _ _
      simp [open_tt_rec]
  | typ_arrow T1 T2 ih1 ih2 =>
      intro j V U i hneq h
      simp [open_tt_rec] at h ⊢
      rcases h with ⟨h1, h2⟩
      exact ⟨ih1 j V U i hneq h1, ih2 j V U i hneq h2⟩
  | typ_all T1 T2 ih1 ih2 =>
      intro j V U i hneq h
      simp [open_tt_rec] at h ⊢
      rcases h with ⟨h1, h2⟩
      have hneq' : i + 1 ≠ j + 1 := by
        intro hs
        apply hneq
        exact Nat.succ.inj hs
      exact ⟨ih1 j V U i hneq h1, ih2 (j + 1) V U (i + 1) hneq' h2⟩

-- Coq line 438: Lemma open_tt_rec_type
theorem open_tt_rec_type : ∀ T U,
  DefType T → ∀ k, T = open_tt_rec k U T := by
  intro T U hT
  induction hT with
  | type_top =>
      intro k
      simp [open_tt_rec]
  | type_var X =>
      intro k
      simp [open_tt_rec]
  | type_arrow T1 T2 _ _ ih1 ih2 =>
      intro k
      have h1 : T1 = open_tt_rec k U T1 := ih1 k
      have h2 : T2 = open_tt_rec k U T2 := ih2 k
      calc
        Typ.typ_arrow T1 T2 = Typ.typ_arrow (open_tt_rec k U T1) (open_tt_rec k U T2) := by
          conv_lhs => rw [h1, h2]
        _ = open_tt_rec k U (Typ.typ_arrow T1 T2) := by
          rfl
  | type_all L T1 T2 hT1 hT2 ih1 ih2 =>
      intro k
      have h1 : T1 = open_tt_rec k U T1 := ih1 k
      rcases var_fresh L with ⟨X, hX⟩
      have hopen : open_tt_rec 0 (typ_fvar X) T2 =
          open_tt_rec (k + 1) U (open_tt_rec 0 (typ_fvar X) T2) := by
        simpa [open_tt] using ih2 X hX (k + 1)
      have h2 : T2 = open_tt_rec (k + 1) U T2 := by
        have hneq : k + 1 ≠ 0 := by exact Nat.succ_ne_zero k
        exact open_tt_rec_type_core T2 0 (typ_fvar X) U (k + 1) hneq hopen
      calc
        Typ.typ_all T1 T2 = Typ.typ_all (open_tt_rec k U T1) (open_tt_rec (k + 1) U T2) := by
          conv_lhs => rw [h1, h2]
        _ = open_tt_rec k U (Typ.typ_all T1 T2) := by
          rfl

-- Coq line 447: Lemma subst_tt_fresh
theorem subst_tt_fresh : ∀ Z U T,
  Z ∉ fv_tt T → subst_tt Z U T = T := by
  intro Z U T
  induction T with
  | typ_top => intro _; simp [subst_tt]
  | typ_bvar n => intro _; simp [subst_tt]
  | typ_fvar X => 
    intro h
    simp [fv_tt] at h
    simp only [subst_tt]
    split_ifs with heq
    · subst heq; simp at h
    · rfl
  | typ_arrow T1 T2 ih1 ih2 =>
    intro h
    simp [fv_tt] at h
    simp [subst_tt, ih1 h.1, ih2 h.2]
  | typ_all T1 T2 ih1 ih2 =>
    intro h
    simp [fv_tt] at h
    simp [subst_tt, ih1 h.1, ih2 h.2]

-- Coq line 456: Lemma subst_tt_open_tt_rec
theorem subst_tt_open_tt_rec : ∀ T1 T2 X P n, DefType P →
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1) := by
  intro T1
  induction T1 with
  | typ_top =>
      intro T2 X P n _
      simp [open_tt_rec, subst_tt]
  | typ_bvar j =>
      intro T2 X P n _
      by_cases hnj : n = j
      · simp [open_tt_rec, subst_tt, hnj]
      · simp [open_tt_rec, subst_tt, hnj]
  | typ_fvar Y =>
      intro T2 X P n hP
      by_cases hYX : Y = X
      · cases hYX
        have hopen : P = open_tt_rec n (subst_tt Y P T2) P :=
          open_tt_rec_type P (subst_tt Y P T2) hP n
        simpa [open_tt_rec, subst_tt] using hopen
      · simp [open_tt_rec, subst_tt, hYX]
  | typ_arrow T11 T12 ih1 ih2 =>
      intro T2 X P n hP
      simp [open_tt_rec, subst_tt, ih1 T2 X P n hP, ih2 T2 X P n hP]
  | typ_all T11 T12 ih1 ih2 =>
      intro T2 X P n hP
      simp [open_tt_rec, subst_tt, ih1 T2 X P n hP, ih2 T2 X P (n + 1) hP]

-- Coq line 466: Lemma subst_tt_open_tt
theorem subst_tt_open_tt : ∀ T1 T2 X P, DefType P →
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2) := by
  intro T1 T2 X P HP
  simp only [open_tt]
  exact subst_tt_open_tt_rec T1 T2 X P 0 HP

-- Coq line 476: Lemma subst_tt_open_tt_var
theorem subst_tt_open_tt_var : ∀ X Y U T, Y ≠ X → DefType U →
  open_tt (subst_tt X U T) (typ_fvar Y) = subst_tt X U (open_tt T (typ_fvar Y)) := by
  intro X Y U T Hneq HU
  rw [subst_tt_open_tt _ _ _ _ HU]
  simp only [subst_tt]
  split_ifs with h
  · subst h; contradiction
  · rfl

-- Coq line 486: Lemma subst_tt_intro
theorem subst_tt_intro : ∀ X T2 U,
  X ∉ fv_tt T2 → DefType U →
  open_tt T2 U = subst_tt X U (T2 open_tt_var X) := by
  intro X T2 U Hfresh HU
  rw [subst_tt_open_tt _ _ _ _ HU]
  simp only [subst_tt]
  split_ifs with h
  · congr 1
    exact (subst_tt_fresh X U T2 Hfresh).symm
  · contradiction

-- Properties of type substitution in terms

-- Coq line 498: Lemma open_te_rec_term_core
theorem open_te_rec_term_core : ∀ e j u i P,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) →
  e = open_te_rec i P e := by
  intro e
  induction e with
  | trm_bvar n =>
      intro j u i P _
      simp [open_te_rec]
  | trm_fvar x =>
      intro j u i P _
      simp [open_te_rec]
  | trm_abs V e1 ih =>
      intro j u i P h
      simp [open_ee_rec, open_te_rec] at h ⊢
      rcases h with ⟨hV, hE⟩
      refine ⟨hV, ?_⟩
      exact ih (j + 1) u i P hE
  | trm_app e1 e2 ih1 ih2 =>
      intro j u i P h
      simp [open_ee_rec, open_te_rec] at h ⊢
      rcases h with ⟨h1, h2⟩
      exact ⟨ih1 j u i P h1, ih2 j u i P h2⟩
  | trm_tabs V e1 ih =>
      intro j u i P h
      simp [open_ee_rec, open_te_rec] at h ⊢
      rcases h with ⟨hV, hE⟩
      refine ⟨hV, ?_⟩
      exact ih j u (i + 1) P hE
  | trm_tapp e1 V ih =>
      intro j u i P h
      simp [open_ee_rec, open_te_rec] at h ⊢
      rcases h with ⟨h1, hV⟩
      exact ⟨ih j u i P h1, hV⟩

-- Coq line 505: Lemma open_te_rec_type_core
theorem open_te_rec_type_core : ∀ e j Q i P, i ≠ j →
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) →
  e = open_te_rec i P e := by
  intro e
  induction e with
  | trm_bvar n =>
      intro j Q i P _ _
      simp [open_te_rec]
  | trm_fvar x =>
      intro j Q i P _ _
      simp [open_te_rec]
  | trm_abs V e1 ih =>
      intro j Q i P hneq h
      simp [open_te_rec] at h ⊢
      rcases h with ⟨hV, hE⟩
      have hV' : V = open_tt_rec i P V := open_tt_rec_type_core V j Q P i hneq hV
      refine ⟨hV', ?_⟩
      exact ih j Q i P hneq hE
  | trm_app e1 e2 ih1 ih2 =>
      intro j Q i P hneq h
      simp [open_te_rec] at h ⊢
      rcases h with ⟨h1, h2⟩
      exact ⟨ih1 j Q i P hneq h1, ih2 j Q i P hneq h2⟩
  | trm_tabs V e1 ih =>
      intro j Q i P hneq h
      simp [open_te_rec] at h ⊢
      rcases h with ⟨hV, hE⟩
      have hV' : V = open_tt_rec i P V := open_tt_rec_type_core V j Q P i hneq hV
      have hneq' : i + 1 ≠ j + 1 := by
        intro hs
        apply hneq
        exact Nat.succ.inj hs
      refine ⟨hV', ?_⟩
      exact ih (j + 1) Q (i + 1) P hneq' hE
  | trm_tapp e1 V ih =>
      intro j Q i P hneq h
      simp [open_te_rec] at h ⊢
      rcases h with ⟨h1, hV⟩
      have hV' : V = open_tt_rec i P V := open_tt_rec_type_core V j Q P i hneq hV
      exact ⟨ih j Q i P hneq h1, hV'⟩

-- Coq line 514: Lemma open_te_rec_term
theorem open_te_rec_term : ∀ e U,
  DefTerm e → ∀ k, e = open_te_rec k U e := by
  intro e U hE
  induction hE with
  | term_var x =>
      intro k
      simp [open_te_rec]
  | term_abs L V e1 hV hBody ihBody =>
      intro k
      have hV' : V = open_tt_rec k U V := open_tt_rec_type V U hV k
      rcases var_fresh L with ⟨x, hx⟩
      have hopen : open_ee e1 (trm_fvar x) = open_te_rec k U (open_ee e1 (trm_fvar x)) :=
        ihBody x hx k
      have hE1 : e1 = open_te_rec k U e1 :=
        open_te_rec_term_core e1 0 (trm_fvar x) k U hopen
      calc
        trm_abs V e1 = trm_abs (open_tt_rec k U V) (open_te_rec k U e1) := by
          conv_lhs => rw [hV', hE1]
        _ = open_te_rec k U (trm_abs V e1) := by
          rfl
  | term_app e1 e2 _ _ ih1 ih2 =>
      intro k
      calc
        trm_app e1 e2 = trm_app (open_te_rec k U e1) (open_te_rec k U e2) := by
          conv_lhs => rw [ih1 k, ih2 k]
        _ = open_te_rec k U (trm_app e1 e2) := by
          rfl
  | term_tabs L V e1 hV hBody ihBody =>
      intro k
      have hV' : V = open_tt_rec k U V := open_tt_rec_type V U hV k
      rcases var_fresh L with ⟨X, hX⟩
      have hopen : open_te e1 (typ_fvar X) =
          open_te_rec (k + 1) U (open_te e1 (typ_fvar X)) := ihBody X hX (k + 1)
      have hE1 : e1 = open_te_rec (k + 1) U e1 := by
        have hneq : k + 1 ≠ 0 := Nat.succ_ne_zero k
        exact open_te_rec_type_core e1 0 (typ_fvar X) (k + 1) U hneq (by simpa [open_te] using hopen)
      calc
        trm_tabs V e1 = trm_tabs (open_tt_rec k U V) (open_te_rec (k + 1) U e1) := by
          conv_lhs => rw [hV', hE1]
        _ = open_te_rec k U (trm_tabs V e1) := by
          rfl
  | term_tapp e1 V _ hV ih1 =>
      intro k
      have hV' : V = open_tt_rec k U V := open_tt_rec_type V U hV k
      calc
        trm_tapp e1 V = trm_tapp (open_te_rec k U e1) (open_tt_rec k U V) := by
          conv_lhs => rw [ih1 k, hV']
        _ = open_te_rec k U (trm_tapp e1 V) := by
          rfl

-- Coq line 527: Lemma subst_te_fresh
theorem subst_te_fresh : ∀ X U e,
  X ∉ fv_te e → subst_te X U e = e := by
  intro X U e
  induction e with
  | trm_bvar n => intro _; simp [subst_te]
  | trm_fvar x => intro _; simp [subst_te]
  | trm_abs V e1 ih =>
    intro h
    simp [fv_te] at h
    simp [subst_te, subst_tt_fresh X U V h.1, ih h.2]
  | trm_app e1 e2 ih1 ih2 =>
    intro h
    simp [fv_te] at h
    simp [subst_te, ih1 h.1, ih2 h.2]
  | trm_tabs V e1 ih =>
    intro h
    simp [fv_te] at h
    simp [subst_te, subst_tt_fresh X U V h.1, ih h.2]
  | trm_tapp e1 V ih =>
    intro h
    simp [fv_te] at h
    simp [subst_te, subst_tt_fresh X U V h.1, ih h.2]

-- Coq line 535: Lemma subst_te_open_te
theorem subst_te_open_te : ∀ e T X U, DefType U →
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T) := by
  intro e T X U hU
  suffices h : ∀ k, subst_te X U (open_te_rec k T e) =
      open_te_rec k (subst_tt X U T) (subst_te X U e) by
    simpa [open_te] using h 0
  intro k
  induction e generalizing k with
  | trm_bvar n =>
      simp [open_te_rec, subst_te]
  | trm_fvar x =>
      simp [open_te_rec, subst_te]
  | trm_abs V e1 ih =>
      simp [open_te_rec, subst_te, subst_tt_open_tt_rec V T X U k hU, ih]
  | trm_app e1 e2 ih1 ih2 =>
      simp [open_te_rec, subst_te, ih1, ih2]
  | trm_tabs V e1 ih =>
      simp [open_te_rec, subst_te, subst_tt_open_tt_rec V T X U k hU, ih]
  | trm_tapp e1 V ih =>
      simp [open_te_rec, subst_te, subst_tt_open_tt_rec V T X U k hU, ih]

-- Coq line 546: Lemma subst_te_open_te_var
theorem subst_te_open_te_var : ∀ X Y U e, Y ≠ X → DefType U →
  open_te (subst_te X U e) (typ_fvar Y) = subst_te X U (open_te e (typ_fvar Y)) := by
  intro X Y U e hne hU
  have hT : subst_tt X U (Typ.typ_fvar Y) = Typ.typ_fvar Y := by
    classical
    simp [subst_tt, hne]
  have h := subst_te_open_te e (Typ.typ_fvar Y) X U hU
  simpa [hT] using h.symm

-- Coq line 556: Lemma subst_te_intro
theorem subst_te_intro : ∀ X U e,
  X ∉ fv_te e → DefType U →
  open_te e U = subst_te X U (e open_te_var X) := by
  intro X U e hfresh hU
  have h1 := subst_te_open_te e (Typ.typ_fvar X) X U hU
  have hT : subst_tt X U (Typ.typ_fvar X) = U := by
    classical
    simp [subst_tt]
  have h2 : subst_te X U e = e := subst_te_fresh X U e hfresh
  calc
    open_te e U = open_te (subst_te X U e) U := by simpa [h2]
    _ = subst_te X U (open_te e (Typ.typ_fvar X)) := by simpa [hT] using h1.symm

-- Properties of term substitution in terms

-- Coq line 568: Lemma open_ee_rec_term_core
theorem open_ee_rec_term_core : ∀ e j v u i, i ≠ j →
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) →
  e = open_ee_rec i u e := by
  intro e
  induction e with
  | trm_bvar n =>
      intro j v u i hneq h
      by_cases hjn : j = n <;> by_cases hin : i = n
      · subst hjn
        subst hin
        contradiction
      · subst hjn
        simp [open_ee_rec, hin]
      · subst hin
        simp [open_ee_rec, hjn] at h ⊢
        exact h
      · simp [open_ee_rec, hjn, hin]
  | trm_fvar x =>
      intro j v u i _ _
      simp [open_ee_rec]
  | trm_abs T e1 ih =>
      intro j v u i hneq h
      simp [open_ee_rec] at h ⊢
      have hneq' : i + 1 ≠ j + 1 := by
        intro hs
        apply hneq
        exact Nat.succ.inj hs
      exact ih (j + 1) v u (i + 1) hneq' h
  | trm_app e1 e2 ih1 ih2 =>
      intro j v u i hneq h
      simp [open_ee_rec] at h ⊢
      exact ⟨ih1 j v u i hneq h.1, ih2 j v u i hneq h.2⟩
  | trm_tabs T e1 ih =>
      intro j v u i hneq h
      simp [open_ee_rec] at h ⊢
      exact ih j v u i hneq h
  | trm_tapp e1 T ih =>
      intro j v u i hneq h
      simp [open_ee_rec] at h ⊢
      exact ih j v u i hneq h

-- Coq line 576: Lemma open_ee_rec_type_core
theorem open_ee_rec_type_core : ∀ e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) →
  e = open_ee_rec i u e := by
  intro e
  induction e with
  | trm_bvar n =>
      intro j V u i h
      simpa [open_te_rec, open_ee_rec] using h
  | trm_fvar x =>
      intro j V u i _
      simp [open_te_rec, open_ee_rec]
  | trm_abs T e1 ih =>
      intro j V u i h
      simp [open_te_rec, open_ee_rec] at h ⊢
      exact ih j V u (i + 1) h
  | trm_app e1 e2 ih1 ih2 =>
      intro j V u i h
      simp [open_te_rec, open_ee_rec] at h ⊢
      exact ⟨ih1 j V u i h.1, ih2 j V u i h.2⟩
  | trm_tabs T e1 ih =>
      intro j V u i h
      simp [open_te_rec, open_ee_rec] at h ⊢
      exact ih (j + 1) V u i h
  | trm_tapp e1 T ih =>
      intro j V u i h
      simp [open_te_rec, open_ee_rec] at h ⊢
      exact ih j V u i h

-- Coq line 583: Lemma open_ee_rec_term
theorem open_ee_rec_term : ∀ u e,
  DefTerm e → ∀ k, e = open_ee_rec k u e := by
  intro u e hE
  induction hE with
  | term_var x =>
      intro k
      simp [open_ee_rec]
  | term_abs L V e1 hV hBody ihBody =>
      intro k
      rcases var_fresh L with ⟨x, hx⟩
      have hopen : open_ee e1 (trm_fvar x) =
          open_ee_rec (k + 1) u (open_ee e1 (trm_fvar x)) := ihBody x hx (k + 1)
      have hE1 : e1 = open_ee_rec (k + 1) u e1 := by
        have hneq : k + 1 ≠ 0 := Nat.succ_ne_zero k
        exact open_ee_rec_term_core e1 0 (trm_fvar x) u (k + 1) hneq (by simpa [open_ee] using hopen)
      calc
        trm_abs V e1 = trm_abs V (open_ee_rec (k + 1) u e1) := by
          conv_lhs => rw [hE1]
        _ = open_ee_rec k u (trm_abs V e1) := by
          rfl
  | term_app e1 e2 _ _ ih1 ih2 =>
      intro k
      calc
        trm_app e1 e2 = trm_app (open_ee_rec k u e1) (open_ee_rec k u e2) := by
          conv_lhs => rw [ih1 k, ih2 k]
        _ = open_ee_rec k u (trm_app e1 e2) := by
          rfl
  | term_tabs L V e1 hV hBody ihBody =>
      intro k
      rcases var_fresh L with ⟨X, hX⟩
      have hopen : open_te e1 (typ_fvar X) =
          open_ee_rec k u (open_te e1 (typ_fvar X)) := ihBody X hX k
      have hE1 : e1 = open_ee_rec k u e1 :=
        open_ee_rec_type_core e1 0 (typ_fvar X) u k (by simpa [open_te] using hopen)
      calc
        trm_tabs V e1 = trm_tabs V (open_ee_rec k u e1) := by
          conv_lhs => rw [hE1]
        _ = open_ee_rec k u (trm_tabs V e1) := by
          rfl
  | term_tapp e1 V _ _ ih1 =>
      intro k
      calc
        trm_tapp e1 V = trm_tapp (open_ee_rec k u e1) V := by
          conv_lhs => rw [ih1 k]
        _ = open_ee_rec k u (trm_tapp e1 V) := by
          rfl

-- Coq line 595: Lemma subst_ee_fresh
theorem subst_ee_fresh : ∀ x u e,
  x ∉ fv_ee e → subst_ee x u e = e := by
  intro x u e
  induction e with
  | trm_bvar n => intro _; simp [subst_ee]
  | trm_fvar y =>
    intro h
    simp [fv_ee] at h
    simp only [subst_ee]
    split_ifs with heq
    · subst heq; simp at h
    · rfl
  | trm_abs V e1 ih =>
    intro h
    simp [fv_ee] at h
    simp [subst_ee, ih h]
  | trm_app e1 e2 ih1 ih2 =>
    intro h
    simp [fv_ee] at h
    simp [subst_ee, ih1 h.1, ih2 h.2]
  | trm_tabs V e1 ih =>
    intro h
    simp [fv_ee] at h
    simp [subst_ee, ih h]
  | trm_tapp e1 V ih =>
    intro h
    simp [fv_ee] at h
    simp [subst_ee, ih h]

-- Coq line 604: Lemma subst_ee_open_ee
theorem subst_ee_open_ee : ∀ t1 t2 u x, DefTerm u →
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2) := by
  intro t1 t2 u x hu
  suffices h : ∀ k, subst_ee x u (open_ee_rec k t2 t1) =
      open_ee_rec k (subst_ee x u t2) (subst_ee x u t1) by
    simpa [open_ee] using h 0
  intro k
  induction t1 generalizing k with
  | trm_bvar n =>
      by_cases hkn : k = n
      · simp [open_ee_rec, subst_ee, hkn]
      · simp [open_ee_rec, subst_ee, hkn]
  | trm_fvar y =>
      by_cases hyx : y = x
      · subst hyx
        have hopenU : u = open_ee_rec k (subst_ee y u t2) u :=
          open_ee_rec_term (subst_ee y u t2) u hu k
        simpa [subst_ee, open_ee_rec] using hopenU
      · simp [subst_ee, open_ee_rec, hyx]
  | trm_abs V e1 ih =>
      simp [open_ee_rec, subst_ee, ih]
  | trm_app e1 e2 ih1 ih2 =>
      simp [open_ee_rec, subst_ee, ih1, ih2]
  | trm_tabs V e1 ih =>
      simp [open_ee_rec, subst_ee, ih]
  | trm_tapp e1 V ih =>
      simp [open_ee_rec, subst_ee, ih]

-- Coq line 612: Lemma subst_ee_open_ee_var
theorem subst_ee_open_ee_var : ∀ x y u e, y ≠ x → DefTerm u →
  open_ee (subst_ee x u e) (trm_fvar y) =
  subst_ee x u (open_ee e (trm_fvar y)) := by
  intro x y u e hneq hu
  have h := subst_ee_open_ee e (trm_fvar y) u x hu
  calc
    open_ee (subst_ee x u e) (trm_fvar y)
        = open_ee (subst_ee x u e) (subst_ee x u (trm_fvar y)) := by
            simp [subst_ee, hneq]
    _ = subst_ee x u (open_ee e (trm_fvar y)) := by
          simpa using h.symm

-- Coq line 636: Lemma subst_ee_intro
theorem subst_ee_intro : ∀ x e u,
  x ∉ fv_ee e → DefTerm u →
  open_ee e u = subst_ee x u (open_ee e (trm_fvar x)) := by
  intro x e u hfresh hu
  have hopen := subst_ee_open_ee e (trm_fvar x) u x hu
  have hfreshEq : subst_ee x u e = e := subst_ee_fresh x u e hfresh
  have hvar : subst_ee x u (trm_fvar x) = u := by
    simp [subst_ee]
  calc
    open_ee e u = open_ee (subst_ee x u e) u := by simpa [hfreshEq]
    _ = open_ee (subst_ee x u e) (subst_ee x u (trm_fvar x)) := by simpa [hvar]
    _ = subst_ee x u (open_ee e (trm_fvar x)) := by simpa using hopen.symm

-- Coq line 637: Lemma subst_te_open_ee_var
theorem subst_te_open_ee_var : ∀ Z P x e,
  open_ee (subst_te Z P e) (trm_fvar x) = subst_te Z P (open_ee e (trm_fvar x)) := by
  intro Z P x
  simp only [open_ee]
  -- Need to prove the general version with open_ee_rec
  intro e
  suffices h : ∀ k, open_ee_rec k (trm_fvar x) (subst_te Z P e) = 
                     subst_te Z P (open_ee_rec k (trm_fvar x) e) by
    exact h 0
  intro k
  induction e generalizing k with
  | trm_bvar n =>
    simp [open_ee_rec, subst_te]
    split_ifs <;> rfl
  | trm_fvar y =>
    simp [open_ee_rec, subst_te]
  | trm_abs V e1 ih =>
    simp only [open_ee_rec, subst_te]
    congr 1
    exact ih (k + 1)
  | trm_app e1 e2 ih1 ih2 =>
    simp [open_ee_rec, subst_te, ih1, ih2]
  | trm_tabs V e1 ih =>
    simp [open_ee_rec, subst_te, ih]
  | trm_tapp e1 V ih =>
    simp [open_ee_rec, subst_te, ih]

-- Coq line 626: Lemma subst_ee_open_te_var
theorem subst_ee_open_te_var : ∀ z u e V, DefTerm u →
  open_te (subst_ee z u e) V = subst_ee z u (open_te e V) := by
  intro z u e V hu
  suffices h : ∀ k, open_te_rec k V (subst_ee z u e) = subst_ee z u (open_te_rec k V e) by
    simpa [open_te] using h 0
  intro k
  induction e generalizing k with
  | trm_bvar n =>
      simp [open_te_rec, subst_ee]
  | trm_fvar x =>
      by_cases hx : x = z
      · subst hx
        simp [subst_ee, open_te_rec]
        symm
        exact open_te_rec_term u V hu k
      · simp [subst_ee, open_te_rec, hx]
  | trm_abs T e1 ih =>
      simp [open_te_rec, subst_ee, ih]
  | trm_app e1 e2 ih1 ih2 =>
      simp [open_te_rec, subst_ee, ih1, ih2]
  | trm_tabs T e1 ih =>
      simp [open_te_rec, subst_ee, ih]
  | trm_tapp e1 T ih =>
      simp [open_te_rec, subst_ee, ih]

-- Substitutions preserve local closure

-- Coq line 657: Lemma subst_tt_type
theorem subst_tt_type : ∀ T Z P,
  DefType T → DefType P → DefType (subst_tt Z P T) := by
  intro T Z P hT hP
  induction hT generalizing Z P with
  | type_top =>
      exact DefType.type_top
  | type_var X =>
      by_cases hXZ : X = Z
      · subst hXZ
        simpa [subst_tt] using hP
      · simpa [subst_tt, hXZ] using (DefType.type_var X)
  | type_arrow T1 T2 hT1 hT2 ih1 ih2 =>
      exact DefType.type_arrow (subst_tt Z P T1) (subst_tt Z P T2) (ih1 Z P hP) (ih2 Z P hP)
  | type_all L T1 T2 hT1 hT2 ih1 ih2 =>
      apply DefType.type_all (insert Z L) (subst_tt Z P T1) (subst_tt Z P T2)
      · exact ih1 Z P hP
      · intro X hX
        have hXL : X ∉ L := by
          intro hXL'
          apply hX
          simp [Finset.mem_insert, hXL']
        have hXZ : X ≠ Z := by
          intro hXZ'
          apply hX
          simp [Finset.mem_insert, hXZ']
        have hBody : DefType (subst_tt Z P (T2 open_tt_var X)) :=
          ih2 X hXL Z P hP
        have hopen : open_tt (subst_tt Z P T2) (typ_fvar X) =
            subst_tt Z P (open_tt T2 (typ_fvar X)) :=
          subst_tt_open_tt_var Z X P T2 hXZ hP
        rw [hopen]
        exact hBody

-- Coq line 665: Lemma subst_te_term
theorem subst_te_term : ∀ e Z P,
  DefTerm e → DefType P → DefTerm (subst_te Z P e) := by
  sorry -- Complex proof with substitution under binders

-- Coq line 673: Lemma subst_ee_term
theorem subst_ee_term : ∀ e1 Z e2,
  DefTerm e1 → DefTerm e2 → DefTerm (subst_ee Z e2 e1) := by
  sorry -- Complex proof with substitution under binders

-- Properties of well-formedness of a type in an environment

-- Coq line 690: Lemma wft_type
theorem wft_type : ∀ E T,
  Wft E T → DefType T := by
  intro E T H
  induction H with
  | wft_top E => exact DefType.type_top
  | wft_var U E X Hbind => exact DefType.type_var X
  | wft_arrow E T1 T2 H1 H2 ih1 ih2 => exact DefType.type_arrow T1 T2 ih1 ih2
  | wft_all L E T1 T2 H1 H2 ih1 ih2 =>
    apply DefType.type_all L T1 T2
    · exact ih1
    · intro X HX
      exact ih2 X HX

-- Coq line 698: Lemma wft_weaken
theorem wft_weaken : ∀ G T E F,
  Wft (E ++ G) T →
  ok (E ++ F ++ G) →
  Wft (E ++ F ++ G) T := by
  sorry

-- Coq line 713: Lemma wft_narrow
theorem wft_narrow : ∀ V F U T E X,
  Wft (E ++ [(X, bind_sub V)] ++ F) T →
  ok (E ++ [(X, bind_sub U)] ++ F) →
  Wft (E ++ [(X, bind_sub U)] ++ F) T := by
  sorry

-- Coq line 730: Lemma wft_strengthen
theorem wft_strengthen : ∀ E F x U T,
  Wft (E ++ [(x, bind_typ U)] ++ F) T → Wft (E ++ F) T := by
  sorry

-- Coq line 747: Lemma wft_subst_tb
theorem wft_subst_tb : ∀ F Q E Z P T,
  Wft (E ++ [(Z, bind_sub Q)] ++ F) T →
  Wft E P →
  ok (E ++ map_subst_tb Z P F) →
  Wft (E ++ map_subst_tb Z P F) (subst_tt Z P T) := by
  sorry

-- Coq line 773: Lemma wft_open
theorem wft_open : ∀ E U T1 T2,
  ok E →
  Wft E (typ_all T1 T2) →
  Wft E U →
  Wft E (open_tt T2 U) := by
  intro E U T1 T2 HE Hall HU
  cases Hall with
  | wft_all L E' T1' T2' HT1 HT2 =>
    -- Need to pick a fresh variable and instantiate
    sorry -- Need to handle cofinite quantification

-- Relations between well-formed environment and types well-formed in environments

-- Helper lemma: binds is preserved by weakening
theorem binds_weaken : ∀ (x : Var) (b : Bind) (E F G : Env),
  (E ++ G).lookup x = some b →
  (E ++ F ++ G).lookup x = some b := by
  sorry -- Complex list induction

-- Coq line 795: Lemma ok_from_okt
theorem ok_from_okt : ∀ E,
  Okt E → ok E := by
  sorry -- This depends on the axiomatized ok predicate

-- Coq line 805: Lemma wft_from_env_has_sub
theorem wft_from_env_has_sub : ∀ x U E,
  Okt E → E.lookup x = some (bind_sub U) → Wft E U := by
  sorry -- Requires weakening lemma

-- Coq line 824: Lemma wft_from_env_has_typ
theorem wft_from_env_has_typ : ∀ x U E,
  Okt E → E.lookup x = some (bind_typ U) → Wft E U := by
  sorry -- Requires weakening lemma

-- Coq line 843: Lemma wft_from_okt_typ
theorem wft_from_okt_typ : ∀ x T E,
  Okt ((x, bind_typ T) :: E) → Wft E T := by
  intro x T E H
  cases H with
  | okt_typ _ _ _ _ HT _ => exact HT

-- Coq line 852: Lemma wft_from_okt_sub
theorem wft_from_okt_sub : ∀ x T E,
  Okt ((x, bind_sub T) :: E) → Wft E T := by
  intro x T E H
  cases H with
  | okt_sub _ _ _ _ HT _ => exact HT

-- Coq line 863: Lemma wft_weaken_right
theorem wft_weaken_right : ∀ T E F,
  Wft E T →
  ok (E ++ F) →
  Wft (E ++ F) T := by
  sorry -- Need to handle the argument order for wft_weaken

-- Properties of well-formedness of an environment

-- Simple lemma: empty environment is Okt
theorem okt_empty : Okt [] := by
  exact Okt.okt_empty

-- Coq line 882: Lemma okt_push_inv
theorem okt_push_inv : ∀ E X B,
  Okt ((X, B) :: E) → ∃ T, B = bind_sub T ∨ B = bind_typ T := by
  intro E X B H
  cases H with
  | okt_sub E' X' T' _ _ _ => 
    use T'; left; rfl
  | okt_typ E' x' T' _ _ _ => 
    use T'; right; rfl

-- Coq line 891: Lemma okt_push_sub_inv
theorem okt_push_sub_inv : ∀ E X T,
  Okt ((X, bind_sub T) :: E) → Okt E ∧ Wft E T ∧ E.lookup X = none := by
  intro E X T H
  cases H with
  | okt_sub _ _ _ HE HT Hfresh => exact ⟨HE, HT, Hfresh⟩

-- Coq line 900: Lemma okt_push_sub_type
theorem okt_push_sub_type : ∀ E X T,
  Okt ((X, bind_sub T) :: E) → DefType T := by
  intro E X T H
  obtain ⟨_, HT, _⟩ := okt_push_sub_inv E X T H
  exact wft_type E T HT

-- Coq line 904: Lemma okt_push_typ_inv
theorem okt_push_typ_inv : ∀ E x T,
  Okt ((x, bind_typ T) :: E) → Okt E ∧ Wft E T ∧ E.lookup x = none := by
  intro E x T H
  cases H with
  | okt_typ _ _ _ HE HT Hfresh => exact ⟨HE, HT, Hfresh⟩

-- Coq line 913: Lemma okt_push_typ_type
theorem okt_push_typ_type : ∀ E X T,
  Okt ((X, bind_typ T) :: E) → DefType T := by
  intro E X T H
  obtain ⟨_, HT, _⟩ := okt_push_typ_inv E X T H
  exact wft_type E T HT

-- Coq line 921: Lemma okt_narrow
theorem okt_narrow : ∀ V E F U X,
  Okt (E ++ [(X, bind_sub V)] ++ F) →
  Wft E U →
  Okt (E ++ [(X, bind_sub U)] ++ F) := by
  sorry

-- Coq line 938: Lemma okt_strengthen
theorem okt_strengthen : ∀ x T E F,
  Okt (E ++ [(x, bind_typ T)] ++ F) →
  Okt (E ++ F) := by
  sorry

-- Coq line 954: Lemma okt_subst_tb
theorem okt_subst_tb : ∀ Q Z P E F,
  Okt (E ++ [(Z, bind_sub Q)] ++ F) →
  Wft E P →
  Okt (E ++ map_subst_tb Z P F) := by
  sorry

-- Coq line 979: Lemma notin_fv_tt_open
theorem notin_fv_tt_open : ∀ Y X T,
  X ∉ fv_tt (T open_tt_var Y) →
  X ∉ fv_tt T := by
  sorry -- Complex proof with set membership reasoning

-- Coq line 989: Lemma notin_fv_wf
theorem notin_fv_wf : ∀ E X T,
  Wft E T → X ∉ Env.domOf E → X ∉ fv_tt T := by
  sorry

-- Coq line 999: Lemma map_subst_tb_id
theorem map_subst_tb_id : ∀ G Z P,
  Okt G → Z ∉ Env.domOf G → G = map_subst_tb Z P G := by
  sorry -- Need properties of subst_tt when variable not free

-- Regularity of relations

-- Coq line 1014: Lemma sub_regular
theorem sub_regular : ∀ E S T,
  Sub E S T → Okt E ∧ Wft E S ∧ Wft E T := by
  sorry -- Complex proof with environment extensions in sub_all case

-- Coq line 1025: Lemma typing_regular
theorem typing_regular : ∀ E e T,
  Typing E e T → Okt E ∧ DefTerm e ∧ Wft E T := by
  sorry -- Complex proof with multiple cases

-- Coq line 1062: Lemma value_regular
theorem value_regular : ∀ t,
  Value t → DefTerm t := by
  intro t Hval
  cases Hval with
  | value_abs V e1 Hterm => exact Hterm
  | value_tabs V e1 Hterm => exact Hterm

-- Coq line 1070: Lemma red_regular
theorem red_regular : ∀ t t',
  Red t t' → DefTerm t ∧ DefTerm t' := by
  sorry -- Complex proof needing substitution lemmas

-- Properties of Subtyping

-- Coq line 1122: Lemma sub_reflexivity
theorem sub_reflexivity : ∀ E T,
  Okt E →
  Wft E T →
  Sub E T T := by
  sorry -- Requires careful induction on Wft structure

-- Coq line 1135: Lemma sub_weakening
theorem sub_weakening : ∀ E F G S T,
  Sub (E ++ G) S T →
  Okt (E ++ F ++ G) →
  Sub (E ++ F ++ G) S T := by
  sorry

-- Narrowing and transitivity

-- Coq line 1152: Definition transitivity_on
def transitivity_on (Q : Typ) : Prop := ∀ E S T,
  Sub E S Q → Sub E Q T → Sub E S T

-- Coq line 1159: Lemma sub_narrowing_aux
theorem sub_narrowing_aux : ∀ Q F E Z P S T,
  transitivity_on Q →
  Sub (E ++ [(Z, bind_sub Q)] ++ F) S T →
  Sub E P Q →
  Sub (E ++ [(Z, bind_sub P)] ++ F) S T := by
  sorry

-- Coq line 1183: Lemma sub_transitivity
theorem sub_transitivity : ∀ Q,
  transitivity_on Q := by
  sorry

-- Coq line 1203: Lemma sub_narrowing
theorem sub_narrowing : ∀ Q E F Z P S T,
  Sub E P Q →
  Sub (E ++ [(Z, bind_sub Q)] ++ F) S T →
  Sub (E ++ [(Z, bind_sub P)] ++ F) S T := by
  sorry

-- Coq line 1218: Lemma sub_through_subst_tt
theorem sub_through_subst_tt : ∀ Q E F Z S T P,
  Sub (E ++ [(Z, bind_sub Q)] ++ F) S T →
  Sub E P Q →
  Sub (E ++ map_subst_tb Z P F) (subst_tt Z P S) (subst_tt Z P T) := by
  sorry

-- Properties of Typing

-- Coq line 1254: Lemma typing_weakening
theorem typing_weakening : ∀ E F G e T,
  Typing (E ++ G) e T →
  Okt (E ++ F ++ G) →
  Typing (E ++ F ++ G) e T := by
  sorry

-- Coq line 1273: Lemma sub_strengthening
theorem sub_strengthening : ∀ x U E F S T,
  Sub (E ++ [(x, bind_typ U)] ++ F) S T →
  Sub (E ++ F) S T := by
  sorry

-- Coq line 1288: Lemma typing_narrowing
theorem typing_narrowing : ∀ Q E F X P e T,
  Sub E P Q →
  Typing (E ++ [(X, bind_sub Q)] ++ F) e T →
  Typing (E ++ [(X, bind_sub P)] ++ F) e T := by
  sorry

-- Coq line 1306: Lemma typing_through_subst_ee
theorem typing_through_subst_ee : ∀ U E F x T e u,
  Typing (E ++ [(x, bind_typ U)] ++ F) e T →
  Typing E u U →
  Typing (E ++ F) (subst_ee x u e) T := by
  sorry

-- Coq line 1329: Lemma typing_through_subst_te
theorem typing_through_subst_te : ∀ Q E F Z e T P,
  Typing (E ++ [(Z, bind_sub Q)] ++ F) e T →
  Sub E P Q →
  Typing (E ++ map_subst_tb Z P F) (subst_te Z P e) (subst_tt Z P T) := by
  sorry

-- Preservation

-- Coq line 1359: Lemma typing_inv_abs
theorem typing_inv_abs : ∀ E S1 e1 T,
  Typing E (trm_abs S1 e1) T →
  ∀ U1 U2, Sub E T (typ_arrow U1 U2) →
     Sub E U1 S1
  ∧ ∃ S2, ∃ L : Finset Var, ∀ x, x ∉ L →
     Typing ((x, bind_typ S1) :: E) (open_ee e1 (trm_fvar x)) S2 ∧ Sub E S2 U2 := by
  sorry

-- Coq line 1371: Lemma typing_inv_tabs
theorem typing_inv_tabs : ∀ E S1 e1 T,
  Typing E (trm_tabs S1 e1) T →
  ∀ U1 U2, Sub E T (typ_all U1 U2) →
     Sub E U1 S1
  ∧ ∃ S2, ∃ L : Finset Var, ∀ X, X ∉ L →
     Typing ((X, bind_sub U1) :: E) (open_te e1 (typ_fvar X)) (open_tt S2 (typ_fvar X))
     ∧ Sub ((X, bind_sub U1) :: E) (open_tt S2 (typ_fvar X)) (open_tt U2 (typ_fvar X)) := by
  sorry

-- Coq line 1391: Lemma preservation_result
theorem preservation_result : preservation := by
  simp only [preservation]
  intro e e' T Hred Htype
  -- This requires the preservation lemma logic
  sorry -- Complex proof requiring all the Typing preservation lemmas

-- Progress

-- Coq line 1426: Lemma canonical_form_abs
theorem canonical_form_abs : ∀ t U1 U2,
  Value t → Typing [] t (typ_arrow U1 U2) →
  ∃ V e1, t = trm_abs V e1 := by
  sorry -- Requires Typing and Sub inversion lemmas

-- Coq line 1439: Lemma canonical_form_tabs
theorem canonical_form_tabs : ∀ t U1 U2,
  Value t → Typing [] t (typ_all U1 U2) →
  ∃ V e1, t = trm_tabs V e1 := by
  sorry -- Requires Typing and Sub inversion lemmas

-- Coq line 1455: Lemma progress_result
theorem progress_result : progress := by
  simp only [progress]
  intro e T Htype
  sorry -- Complex proof requiring canonical forms and Typing inversion

end Lp2lc.Active.Fsub
