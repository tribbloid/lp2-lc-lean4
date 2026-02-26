import «Lp2lc».Active.STLC.Def

namespace Lp2lc.Active.STLC

open Typ
open Trm
open valid_ctx
open typing
open lc
open beta_red
open para
open multi_red
open multi_para

lemma para_diamond t t1 :
    para t t1 → ∀ t2, para t t2
    → ∃ t', (para t1 t') ∧ (para t2 t') := by
  intro tpt1
  induction tpt1
  case para_var x =>
    intro t2 tpt2
    use t2
    exact ⟨tpt2, lc_para_refl t2 (para_regular _ _ tpt2).2⟩
  case para_red s1 s1' s2 s2' T L _ s2ps2' ih1 ih2 =>
    intro t2 tpt2
    cases tpt2
    case para_red u1' u2' L' f' s2pu2' =>
      let ⟨x, qx⟩ := pick_fresh u2' (L ∪ L' ∪ (fv u1') ∪ (fv s1') ∪ (fv s2'))
      simp at qx
      rw [subst_intro u1' u2' (para_regular _ _ s2pu2').2 x qx.2.2.1]
      rw [subst_intro s1' s2' (para_regular _ _ s2ps2').2 x qx.2.2.2.1]
      have fact1: ∃ t', para s2' t' ∧ para u2' t' := by
        apply ih2 _ s2pu2'
      have fact2 : ∃ t', para (open₀ s1' ($ x)) t' ∧ para (open₀ u1' ($ x)) t' := by
        apply ih1 _ qx.1 _ (f' _ qx.2.1)
      rcases fact1 with ⟨t', qt'⟩
      rcases fact2 with ⟨t'', qt''⟩
      use ([x // t'] t'')
      constructor
      apply para_subst_all _ _ _ _ qt''.1 qt'.1
      apply para_subst_all _ _ _ _ qt''.2 qt'.2
    case para_app u2 u2' s1pu2 s2pu2' =>
      cases s1pu2
      next s1'' L' f' =>
        let ⟨x, qx⟩ := pick_fresh s1' (L ∪ L' ∪ (fv s1''))
        simp at qx
        have fact1: ∃ t', para s2' t' ∧ para u2' t' := by
          apply ih2 _ s2pu2'
        have fact2 : ∃ t', para (open₀ s1' ($ x)) t' ∧ para (open₀ s1'' ($ x)) t' := by
          apply ih1 _ qx.1 _ (f' _ qx.2.1)
        rcases fact1 with ⟨t', qt'⟩
        rcases fact2 with ⟨t'', qt''⟩
        use (open₀ (close₀ t'' x) t')
        constructor
        . apply para_through _ _ _ _ x ⟨qx.2.2.2, by simp [close₀, (close_var_fv t'' x 0)]⟩
          rw [open_close_var _ _ (para_regular _ _ qt''.1).2]
          exact qt''.1
          exact qt'.1
        . apply para_red _ _ _ _ _ (fv (open₀ s1'' ($ x)) ∪ fv t'' ∪ {x})
          intro y qy
          rw [← close_open_var x s1'' qx.2.2.1]
          apply open_close_para _ _ _ _ qt''.2 qy
          exact qt'.2
  case para_app s1 s1' s2 s2' s1ps1' _ ih1 ih2 =>
      intro t2 tpt2
      cases tpt2
      case para_red t1' u1' u2' T L f s2pu2' =>
        cases s1ps1'
        next s1'' L' f' =>
          let ⟨x, qx⟩ := pick_fresh u1' (L ∪ L' ∪ (fv s1''))
          simp at qx
          have fact1: ∃ t', para s2' t' ∧ para u2' t' := by
            apply ih2 _ s2pu2'
          have fact2 : ∃ t', para (λT, s1'') t' ∧ para (λT, u1') t' := by
            apply ih1 (λT, u1') (para_abs _ _ _ L f)
          rcases fact1 with ⟨t', qt'⟩
          rcases fact2 with ⟨t'', qt''⟩
          cases qt''.1
          next w1 L'' f'' =>
            cases qt''.2
            next L''' f''' =>
              use (open₀ w1 t')
              constructor
              . apply para_red _ _ _ _ _ L'' f'' qt'.1
              . apply para_open_out _ _ _ _ L''' f''' qt'.2
      case para_app u1 u2' s1pu1 s2pu2' =>
        have fact1: ∃ t', para s1' t' ∧ para u1 t' := by
          apply ih1 _ s1pu1
        have fact2: ∃ t', para s2' t' ∧ para u2' t' := by
          apply ih2 _ s2pu2'
        rcases fact1 with ⟨t', qt'⟩
        rcases fact2 with ⟨t'', qt''⟩
        use (t' @ t'')
        constructor
        . apply para_app _ _ _ _ qt'.1 qt''.1
        . apply para_app _ _ _ _ qt'.2 qt''.2
  case para_abs s1 s2' T L _ ih =>
    intro t2 tpt2
    cases tpt2
    next t2' L' f' =>
      let ⟨x, qx⟩ := pick_fresh s2' (L ∪ L' ∪ (fv t2'))
      simp at qx
      have fact1 := ih x qx.1 _ (f' x qx.2.1)
      rcases fact1 with ⟨t', qt'⟩
      use (λT, (close₀ t' x))
      constructor
      . apply para_abs _ _ _ (fv (open₀ s2' ($ x)) ∪ fv t' ∪ {x})
        intro y qy
        rw [← close_open_var x s2' qx.2.2.2]
        apply open_close_para _ _ _ _ qt'.1 qy
      . apply para_abs _ _ _ (fv (open₀ t2' ($ x)) ∪ fv t' ∪ {x})
        intro y qy
        rw [← close_open_var x t2' qx.2.2.1]
        apply open_close_para _ _ _ _ qt'.2 qy

lemma multi_para_diamond_core t t1 t2 :
    (para t t1) ∧ (multi_para t t2)
    → ∃ t', (multi_para t1 t') ∧ (para t2 t') := by
  intro ⟨tpt1, tmt2⟩
  induction tmt2
  case m_para_refl _ =>
    use t1
    constructor
    apply m_para_refl
    exact (para_regular _ _ tpt1).2
    exact tpt1
  case m_para_head s1 s2 _ s1ps2 h =>
    rcases h with ⟨t' , ⟨h1, h2⟩⟩
    have q := (para_diamond _ _ s1ps2 _ h2)
    rcases q with ⟨t'', ⟨h3, h4⟩⟩
    use t''
    constructor
    exact (m_para_head _ _ _ h1 h4)
    exact h3

lemma multi_para_diamond t t1 t2 :
    (multi_para t t1) ∧ (multi_para t t2)
    → ∃ t', (multi_para t1 t') ∧ (multi_para t2 t') := by
  intro ⟨tmpt1 , tmpt2⟩
  induction tmpt1
  case m_para_refl _ =>
    use t2
    exact ⟨tmpt2, m_para_refl t2 (multi_para_regular _ _ tmpt2).2⟩
  case m_para_head s1 s2 _ s1ps2 f =>
    rcases f with ⟨t', ⟨h1,h2⟩⟩
    have q := (multi_para_diamond_core _ _ _ ⟨s1ps2, h1⟩)
    rcases q with ⟨t'', ⟨h3, h4⟩⟩
    use t''
    constructor
    exact h3
    exact (m_para_head _ _ _ h2 h4)

theorem beta_red_confluence :
    ∀ t t1 t2, (multi_red t t1) ∧ (multi_red t t2)
    → ∃ t', (multi_red t1 t') ∧ (multi_red t2 t') := by
  intro t t1 t2 ⟨trt1 , trt2⟩
  simp [multi_red_iff_multi_para] at trt1 trt2 ⊢
  exact (multi_para_diamond t t1 t2 ⟨trt1 , trt2⟩)

end Lp2lc.Active.STLC

namespace Lp2lc.Active.STLC

open Typ
open Trm
open beta_red
open multi_red
open lc

namespace Trm

-- Defining substitutions over contexts --
@[simp]
def multi_subst (L : Finset ℕ) (f : L → Trm) : Trm → Trm
| bvar i => bvar i
| fvar y => if h : (y ∈ L) then (f ⟨y, h⟩) else (fvar y)
| abs T u => abs T (multi_subst L f u)
| app u1 u2 => app (multi_subst L f u1) (multi_subst L f u2)

--context_type takes a term in a context and outputs its type
@[simp]
def context_type Γ (x : context_terms Γ) : Typ :=
  match Γ, x with
  | [], ⟨_, h⟩ => by simp [context_terms] at h
  | (x, T) :: Γ, ⟨x', h⟩ =>
    if ha : x' = x then
      T
    else
      context_type Γ ⟨x', by simpa [context_terms, ha] using h⟩

--substitution over the empty context does nothing
lemma multi_subst_over_emp t (f : context_terms [] → Trm) :
    (multi_subst (context_terms []) f t) = t := by
  induction t
  case bvar i =>
    simp
  case fvar x =>
    simp
  case abs T t' ih =>
    simp at ih ⊢
    rw [ih]
  case app t1 t2 ih1 ih2 =>
    simp at ih1 ih2 ⊢
    exact ⟨ih1, ih2⟩

--substitution over [(x,T)] is the same as usual (single) substitution
lemma multi_subst_at_singleton t x T :
    (f : context_terms [(x, T)] → Trm)
    → (multi_subst (context_terms [(x, T)]) f t)
      = ([x // (f ⟨x, by simp⟩)] t) := by
  intro f
  induction t
  case bvar i =>
    simp
  case fvar y =>
    simp
    by_cases h : y = x
    . simp [h]
    . simp [h]
  case abs T t' ih =>
    simp
    exact ih
  case app t1 t2 ih1 ih2 =>
    simp
    exact ⟨ih1, ih2⟩

--if we have a function of terms of a context, say f,
--for a term u and variable x, we can extend the f with mapping x → u
@[simp]
def add_term Γ (f : context_terms Γ → Trm)
    (u : Trm) y T (x : context_terms ((y , T) :: Γ)) : Trm := by
  rcases x with ⟨x' , h⟩
  by_cases p : x' = y
  . exact u
  . simp [p] at h
    exact f ⟨x' , h⟩

--If y does not appear in t, then substitution over a context (y,T) ++ Γ
--is the same as substitution over Γ
lemma multi_subst_fresh Γ t u y T (h : y ∉ (fv t)) (f : context_terms Γ → Trm) :
    (multi_subst (context_terms ((y , T) :: Γ)) (add_term Γ f u y T) t)
     = (multi_subst (context_terms Γ) f t) := by
  induction t
  case bvar i =>
    rfl
  case fvar x =>
    simp [fv] at h
    simp only [multi_subst, context_terms, Finset.mem_union, Finset.mem_singleton, add_term]
    have p : x ≠ y := fun q => h q.symm
    simp [p]
  case abs T u hu =>
    simp only [multi_subst, abs.injEq]
    constructor
    simp only
    exact (hu h)
  case app u1 u2 h1 h2 =>
    simp only [multi_subst, app.injEq]
    simp [fv] at h
    exact ⟨(h1 h.1), (h2 h.2)⟩


--substitution over a context distributes over opening
lemma multi_subst_open_lemma_1 t1 t2 Γ : (f : context_terms Γ → Trm)
   → (∀ x (h : x ∈ context_terms Γ), lc (f ⟨x,h⟩)) → (j : ℕ)
   → (multi_subst (context_terms Γ) f ({j ~> t2} t1))
     = ({j ~> multi_subst (context_terms Γ) f t2} (multi_subst (context_terms Γ) f t1)) := by
  induction t1
  case bvar k =>
    simp
    intros f _ j
    by_cases hjy : (j = k)
    . rw [if_pos, if_pos] <;> exact hjy
    . rw [if_neg, if_neg, multi_subst]
      <;> exact hjy
  case fvar y =>
   intro f lcf j
   by_cases hy : (y ∈ context_terms Γ)
   . simp [opening, multi_subst, hy]
     exact (opening_lc (f ⟨y, hy⟩) _ (lcf y hy) _)
   . simp [opening, multi_subst, hy]
  case abs T u ihu =>
   intro f lcf j
   simp [opening, multi_subst]
   exact (ihu f lcf (j + 1))
  case app u1 u2 ihu1 ihu2 =>
   intro f lcf j
   simp [opening, multi_subst]
   exact ⟨ihu1 f lcf j, ihu2 f lcf j⟩

--special case of previous fact at j=0
lemma multi_subst_open_lemma_2 Γ t u y T : lc u → y ∉ fv t
    → (f : context_terms Γ → Trm)
    → (∀ x (h : x ∈ context_terms Γ), lc (f ⟨x,h⟩))
    → (multi_subst (context_terms ((y , T) :: Γ)) (add_term Γ f u y T) (open₀ t ($ y)))
      = (open₀ (multi_subst (context_terms Γ) f t) u) := by
  intro lcu hy f lcf
  rw [open₀ , multi_subst_open_lemma_1, multi_subst, ← open₀]
  rw [multi_subst_fresh Γ t u y T hy f]
  simp
  intro x h
  by_cases p : x = y
  . simp [p]
    exact lcu
  . simp [p] at h ⊢
    exact lcf x h

--When we open a term, we can instead open the term with a fresh variable and
--then multi-substitute for that variable.
lemma multi_subst_open Γ t y : y ∉ context_terms Γ
    → (f : context_terms Γ → Trm)
    → (∀ x (h : x ∈ context_terms Γ), lc (f ⟨x,h⟩))
    → (multi_subst (context_terms Γ) f (open₀ t ($ y)))
      = (open₀ (multi_subst (context_terms Γ) f t) ($ y)) := by
  intro hy f lcf
  rw [open₀ , multi_subst_open_lemma_1, multi_subst, ← open₀]
  simp [hy]
  apply lcf

--if (x,T) appears in context Γ, then the context map sends Γ x to T
lemma context_type_eq_bind Γ (x : context_terms Γ) T :
    valid_ctx Γ → binds x T Γ → context_type Γ x = T := by
  induction Γ
  case nil =>
    intro _ bnd
    cases bnd
  case cons h Γ' ih =>
    intro vld bnd
    simp only [context_type, context_terms]
    by_cases p : h.1 = ↑x
    . simp [p] at bnd ⊢
      apply bnd
    . have q : (↑x ≠ h.1) := (fun z => p (z.symm))
      simp [q]
      apply ih
      apply valid_remove_cons _ _ _ vld
      apply binds_remove_mid_cons ↑x h.1 T h.2 Γ' [] bnd
      symm
      exact p

--if a term is locally closed, and there is list of locally closed terms, then
--substition with these terms is also locally closed.
lemma multi_subst_lc t Γ : lc t
    → (f : context_terms Γ → Trm)
    → (∀ x (h : x ∈ context_terms Γ), lc (f ⟨x,h⟩))
    → lc ((multi_subst (context_terms Γ) f t)) := by
  intro lct f lcf
  induction lct
  case lc_var y =>
    rw [multi_subst]
    by_cases hxy : y ∈ context_terms Γ
    . simp [if_pos, hxy]
      exact (lcf y hxy)
    . simp [if_neg, hxy]
      exact (lc_var y)
  case lc_abs u T L a hu =>
    simp
    apply lc_abs _ _ (L ∪ (context_terms Γ))
    intro x hx
    simp at hx
    rw [← multi_subst_open Γ u x hx.2 f lcf]
    apply hu x hx.1
  case lc_app u1 u2 lcu1 lcu2 hu1 hu2 =>
    dsimp [multi_subst]
    apply (lc_app _ _ hu1 hu2)

end Trm
end Lp2lc.Active.STLC

namespace Lp2lc.Active.STLC

open Typ
open Trm
open lc
open typing

namespace Trm

--a term is reducible if it reducts
def reducible (t : Trm) : Prop := ∃ t', beta_red t t'

--a term is normal if it is not reducible
def normal (t : Trm) : Prop := ¬ (reducible t)

--a term is normal iff it has no multi-step reduct
lemma normal_has_no_proper_multi_red (t : Trm) :
    normal t → ∀ t', multi_red t t' → t = t' := by
  intro nt t' tmt'
  induction tmt'
  case mr_refl _ =>
    rfl
  case mr_head t2 t3 tmt2 t2bt3 ih =>
    by_contra p
    rw [ih] at nt
    apply nt
    exact ⟨t3, t2bt3⟩

-- a term is normalizable if it has a normal multi-step reduct
def normalizable (t : Trm) : Prop := ∃ t', ((multi_red t t') ∧ (normal t'))

-- a term t is strongly normalizable if any one-step reduction sequence
--starting with t must terminate
def strongly_normalizable (t : Trm) : Prop :=
  ∀ (f : Nat → Trm), (((f 0 = t) ∧ (∀ n, (beta_red (f n) (f (Nat.succ n))))) → False)

--the following is an inductive version of being strongly normalizable
inductive SN : Trm → Prop
  | sn : (∀ t', (beta_red t t') → SN t') → SN t

--Both are logically equivalent
lemma strongly_normalizable_iff_SN t :
    strongly_normalizable t ↔ SN t := by
  constructor
  . contrapose
    intro notsnt
    have this : ∀ u , ¬ SN u → ∃ t', beta_red u t' ∧ ¬ SN t' := by
      intro u notsnu
      by_contra F
      push_neg at F
      apply notsnu (SN.sn F)
    choose f w hw using this
    let f' : Nat → {u // ¬ SN u} := fun n =>
      Nat.iterate (fun (x : {u // ¬ SN u}) => ⟨f x.1 x.2, hw x.1 x.2⟩) n ⟨t, notsnt⟩
    let f'' := (fun n => (f' n).1)
    intro G
    apply G f''
    constructor
    . rfl
    . intro n
      have rel := w (f' n).1 (f' n).2
      have eq1 : ((f' n).1) = (f'' n) := by rw []
      have eq2 : (f (f' n).1 (f' n).2) = (f'' (n + 1)) := by
        simp [f'', f', Function.iterate_succ_apply']
      simp [← eq1, ← eq2, rel]
  . intro snt
    induction snt
    case sn t' _ ih =>
      rintro f ⟨p , F⟩
      let f' : ℕ → Trm := fun n => Nat.rec (f 1) (fun n _ => f (Nat.succ (Nat.succ n))) n
      apply ih (f 1) (by rw [← p]; exact (F 0)) f'
      constructor
      . rfl
      . intro n
        induction n
        case zero =>
          exact (F 1)
        case succ n _ =>
          exact (F (Nat.succ (Nat.succ n)))

--one-step reduction preserves being strongly normalizable
lemma beta_red_preserves_SN (t : Trm) : SN t → ∀ t', beta_red t t' → SN t' := by
  intro snt
  cases snt
  next F =>
    exact F

--multi-step reduction preserves being strongly normalizable
lemma multi_red_preserves_SN (t t' : Trm) : SN t → multi_red t t' → SN t' := by
  intro snt tmt'
  induction tmt'
  case mr_refl _ =>
    exact snt
  case mr_head t2 t3 _ t2bt3 ih =>
    exact (beta_red_preserves_SN _ ih _ t2bt3)

--for a locally closed term s, if applying s to t is strongly normalizing,
--then t is strongly normalizing
lemma SN_app1 t s : lc s → SN (t @ s) → SN t := by
  intro lcs sn2ts
  generalize h : (t @ s) = t' at sn2ts
  induction sn2ts generalizing t with
  | sn F IH =>
    subst h
    apply SN.sn
    intro t' tbt'
    apply IH (t' @ s) (beta_red.br_app1 t t' s lcs tbt') _ rfl

-- If a term has two normal reducts, they must be the same
lemma normal_is_unique (t : Trm) :
    ∀ t1 t2, ((multi_red t t1) ∧ (normal t1)) ∧ ((multi_red t t2) ∧ (normal t2))
    → t1 = t2 := by
  intro t1 t2
  rintro ⟨⟨tmt1, n1⟩ , ⟨tmt2, n2⟩⟩
  have this : ∃ t3, multi_red t1 t3 ∧ multi_red t2 t3 := by
    exact (beta_red_confluence t t1 t2 ⟨tmt1, tmt2⟩)
  rcases this with ⟨t3, ⟨t1mt3, t2mt3⟩⟩
  rw [normal_has_no_proper_multi_red t1 n1 t3 t1mt3]
  rw [normal_has_no_proper_multi_red t2 n2 t3 t2mt3]

-- Definition of strongly computable terms by Jeremy Avigad.
-- This construction is also known as logical relations.
-- The definition is valid for locally closed terms.
@[simp]
def SC : Typ → Set Trm
  | typ_base => {t | (lc t) ∧ SN t}
  | typ_arrow t1 t2 =>
    {t | (lc t) ∧ (∀ u, ((lc u) ∧ (u ∈ SC t1)) → (t @ u) ∈ SC t2)}

-- By definition, strongly computable terms are locally closed.
lemma SC_regular A t : t ∈ (SC A) → lc t := by
  intro H
  induction A
  case typ_base =>
    exact H.1
  case typ_arrow t1 t2 _ _ =>
    exact H.1

-- A term is neutral if it is not an abstraction.
@[simp]
def neutral : Trm → Prop
| bvar _ => true
| fvar _ => true
| abs _ _ => false
| app _ _ => true

-- CR2 says that if t is strongly computable, then any multi-step reduct of t
-- is also strongly computable.
theorem CR2 : ∀ A t, (∀ t', t ∈ SC A → multi_red t t' → t' ∈ SC A) := by
  intro A
  induction A
  case typ_base =>
    intro t t' sct tmt'
    exact ⟨(multi_red_regular _ _ tmt').2, (multi_red_preserves_SN _ _ sct.2 tmt')⟩
  case typ_arrow A1 A2 _ ih2 =>
    intro t t' sct tmt'
    constructor
    . apply (multi_red_regular _ _ tmt').2
    . intro u H
      have this1 : (t @ u) ∈ SC (A2) := (sct.2 u H)
      apply ih2 (t @ u) (t' @ u) this1 (multi_red_app1 _ _ _ ⟨tmt', H.1⟩)

-- CR1 says that strongly computable terms are strongly normalizing.
-- CR3 says that if a locally closed term t is neutral, also any
-- one-step reduct of t is strongly computable, then t is strongly computable.
theorem CR_1_3 : ∀ A t,
    (t ∈ SC A → SN t) ∧ --CR1
    (lc t → neutral t → (∀ t', beta_red t t' → t' ∈ SC A) → t ∈ SC A) := by --CR3
  intro A
  induction A
  case typ_base =>
    intro t
    constructor
    . exact (fun sct => sct.2) --CR1 base case
    . exact (fun lct _ F => ⟨lct, SN.sn (fun s tbs => (F s tbs).2)⟩) --CR3 base case
  case typ_arrow A1 A2 ih1 ih2 =>
    intro t
    constructor
    . rintro ⟨_, H⟩ --CR1 arrow case
      let ⟨x, p2⟩ := pick_fresh t ∅
      simp at p2
      have this2 : ($ x) ∈ SC A1 := by
        apply (ih1 ($ x)).2 (lc_var x) (by simp)
        intro t' nbt
        cases nbt
      have this3 : (app t ($ x)) ∈ SC A2 := H ($ x) ⟨lc_var x , this2⟩
      have this4 : SN (app t ($ x)) := (ih2 (app t ($ x))).1 this3
      apply (SN_app1 _ _ (lc_var x) this4)
    . intro lct nt F --CR3 arrow case
      constructor
      . exact lct
      . intro u Hu
        have this1 : SN u := (ih1 _).1 Hu.2
        induction this1
        case sn u _ ihu =>
        apply (ih2 (t @ u)).2 (lc_app _ _ lct Hu.1) (by simp)
        intro t' tubt'
        cases tubt'
        next a _ _ =>
          simp [neutral] at nt
        next a tba lcu =>
          have this2 : a ∈ SC (A1 -> A2) := (F a tba)
          apply (this2.2 u Hu)
        next c lct ubc =>
          apply ihu c ubc
          constructor
          . apply (beta_red_regular _ _ ubc).2
          . apply CR2 _ _ _ Hu.2 (beta_to_multi_red _ _ ubc)

def CR1 A t := (CR_1_3 A t).1

def CR3 A t := (CR_1_3 A t).2

-- Free variables are always strongly computable.
lemma SC_var A x : ($ x) ∈ SC A := by
  induction A
  case typ_base =>
    constructor
    . apply lc_var x
    . apply SN.sn
      intro t tbx
      cases tbx
  case typ_arrow A1 A2 _ _ =>
    apply CR3 _ _ (lc_var x) (by simp)
    intro t' bred
    cases bred

-- Criteria for strongly computable lambda terms:
-- Suppose for all variable x not occured in t and strongly computable u, we have
-- [x//u]tˣ is strongly computable. Then λt is strongly computable.
theorem SC_lambda A1 A2 t : lc (λA1, t)
    → (∀ u x, x ∉ fv t → u ∈ SC A1 → ([x // u] (open₀ t ($ x))) ∈ SC A2)
    → (λ A1, t) ∈ SC (A1 -> A2) := by
  intro lct F
  have this : (∃ y, (open₀ t ($ y)) ∈ SC A2) := by
    let ⟨y, hy⟩ := pick_fresh t ∅
    simp at hy
    have this : ($ y) ∈ SC A1 := SC_var A1 y
    have this2 : (open₀ t ($ y)) ∈ SC A2 := by
      rw [subst_intro t ($ y) (lc_var y) y hy]
      exact (F ($ y) y hy this)
    exact ⟨y, this2⟩
  rcases this with ⟨y, hy⟩
  constructor
  . exact lct
  . intro u Hu
    have snu := CR1 _ _ Hu.2
    have snt := CR1 _ _ hy
    generalize h : (open₀ t ($ y)) = w at snt
    induction snt generalizing t with
    | sn _ iht' =>
      rw [← h] at iht'
      induction snu
      case sn u _ ihu =>
        apply CR3 _ _ (lc_app _ _ lct Hu.1) (by simp)
        intro t'' bred
        cases bred
        next lct' lcu =>
          let ⟨z, hz⟩ := pick_fresh t {0}
          simp at hz
          push_neg at hz
          rw [subst_intro _ _ Hu.1 z hz.2]
          apply (F u z hz.2 Hu.2)
        next t1' t'bt1' lcu =>
          cases t'bt1'
          next t'' L a =>
            let ⟨x, hx⟩ := pick_fresh t (L ∪ (fv t''))
            simp at hx
            have this3 : beta_red (open₀ t ($ y)) (open₀ t'' ($ y)) := by
              rw [subst_intro t ($ y) (lc_var y) x hx.2.2]
              rw [subst_intro t'' ($ y) (lc_var y) x hx.2.1]
              apply beta_rename _ _ _ _ (a x hx.1)
            apply (iht' (open₀ t'' ($ y)) this3 t''
                (beta_red_regular _ _ (beta_red.br_abs _ _ _ _ a)).2)
            intro u z hz scu
            rw [← subst_intro t'' u (SC_regular _ _ scu) z hz]
            have this4 : open₀ t u ∈ SC A2 := by
              rw [subst_intro t u (SC_regular _ _ scu) x hx.2.2]
              apply F u x hx.2.2 scu
            apply CR2 _ _ _ this4
            apply beta_to_multi_red
            rw [subst_intro t'' u (SC_regular _ _ scu) x hx.2.1]
            rw [subst_intro t u (SC_regular _ _ scu) x hx.2.2]
            apply beta_red_subst_out _ _ _ _ ⟨a x hx.1, (SC_regular _ _ scu)⟩
            apply CR2 _ _ _ hy (beta_to_multi_red _ _ this3)
            rfl
        next u1' lct' ubu1 =>
          apply ihu u1' ubu1
          have this5 := (beta_red_regular _ _ ubu1).2
          exact ⟨this5, CR2 _ _ _ Hu.2 (beta_to_multi_red _ _ ubu1)⟩
          intro t1 bred t2 typ2 F2 op2 q2
          apply CR2
          apply iht' t1 bred _ typ2 F2 op2 q2
          apply (beta_to_multi_red _ _ (beta_red.br_app2 _ _ _ (typ2) ubu1))

-- We can generalize the previous theorem:
-- Suppose for all strongly computable u, the opened term tᵘ is strongly computable.
-- Then λt is strongly computable.
theorem SC_lambda_term A1 A2 t : lc (λ A1,t)
    → (∀ u, u ∈ SC A1 → (open₀ t u) ∈ SC A2)
    → (λ A1, t) ∈ SC (A1 -> A2) := by
  intro lct F
  apply SC_lambda _ _ _ lct
  intro u x fvx scu
  rw [← subst_intro _ _ (SC_regular _ _ scu) x fvx]
  apply F u scu

-- Fundamental lemma about logical relations:
-- Suppose (x1:A1, x2:A2, ..., xn:An) ⊢ t : A. Then for any strongly computable ui:Ai,
-- we have ([x1//u1, x2//u2, ..., xn//un] t) is strongly computable.
lemma SC_subst t A : typing Γ t A
    → (f : (context_terms Γ) → Trm)
    → (∀ x (h : x ∈ (context_terms Γ)), (f ⟨x, h⟩) ∈ SC (context_type Γ ⟨x, h⟩))
    → (multi_subst (context_terms Γ) f t) ∈ SC A := by
  intro typt
  induction typt
  case typ_var Δ y T vld bnd =>
    intro f Hf
    simp only [multi_subst]
    by_cases h : y ∈ context_terms Δ
    . simp [h, ← context_type_eq_bind Δ ⟨y, h⟩ T vld bnd]
      apply (Hf y h)
    . simp [h]
      apply SC_var
  case typ_abs L Δ u T1 T2 a ih =>
    intro f Hf
    apply SC_lambda_term
    rw [← multi_subst]
    apply multi_subst_lc _ _ (typing_regular _ _ _ (typ_abs L Δ u T1 T2 a))
    exact (fun x hx => (SC_regular _ _ (Hf x hx)))
    intros u1 scu1
    let ⟨x, hx⟩ := pick_fresh u L
    simp at hx
    have this : (∀ y (s : y ∈ (context_terms ((x, T1) :: Δ))),
        ((add_term Δ f u1 x T1) ⟨y, s⟩) ∈ SC (context_type ((x, T1) :: Δ) ⟨y, s⟩)) := by
      intro y s
      by_cases p : y = x
      . simp [p, scu1]
      . simp [p] at s ⊢
        apply Hf y s
    have this2 := ih x hx.1 (add_term Δ f u1 x T1) this
    rw [multi_subst_open_lemma_2] at this2
    exact this2
    apply (SC_regular _ _ scu1)
    apply hx.2
    exact (fun y s => (SC_regular _ _ (Hf y s)))
  case typ_app Δ t1 t2 T1 T2 _ typt2 ih1 ih2 =>
    intro f Hf
    cases (ih1 f Hf)
    next L R =>
      apply R (multi_subst (context_terms Δ) f t2)
      constructor
      . apply multi_subst_lc
        apply (typing_regular _ _ _ typt2)
        exact (fun x hx => (SC_regular _ _ (Hf x hx)))
      . apply (ih2 f Hf)

-- Final theorem:
-- By CR1 and substitution lemma, we have every typeable term is strongly normalizing.
theorem strong_normalization t T : typing [] t T → SN t := by
  intro typt
  apply CR1 T t
  let ⟨x, hx⟩ := pick_fresh t ∅
  simp at hx
  let f : context_terms [(x, T)] → Trm := fun _ => ($ x)
  have this : multi_subst (context_terms [(x, T)]) f t = t := by
    rw [multi_subst_at_singleton]
    rw [subst_fresh _ _ _ hx]
  rw [← this]
  apply SC_subst
  apply typing_weakening [] [(x, T)] _ _ typt
  apply valid_push _ _ _ (valid_ctx.valid_nil) (by simp)
  exact (fun y hy => SC_var _ _)

end Trm
end Lp2lc.Active.STLC

namespace Lp2lc.Active.STLC

open Typ
open Trm
open List
open typing
open valid_ctx
open lc

theorem typing_unique :
    ∀ t, lc t → ∀ Γ T1 T2,
    typing Γ t T1 → typing Γ t T2 → T1 = T2 := by
  intro t lct
  induction lct
  case lc_var x =>
    intro Γ T1 T2 ty1 ty2
    cases ty1
    next _ bnd =>
      cases ty2
      next _ bnd' =>
        simp [binds] at bnd bnd'
        rw [bnd] at bnd'
        simp at bnd'
        exact bnd'
  case lc_abs u T L a ih =>
    intro Γ T1 T2 ty1 ty2
    cases ty1
    next L1 U1 h1 =>
      cases ty2
      next L2 U2 h2 =>
        have ⟨x,hx⟩ := pick_fresh u (L ∪ L1 ∪ L2)
        simp at hx ⊢
        apply ih x hx.1 ((x,T) :: Γ) U1 U2 (h1 x hx.2.1) (h2 x hx.2.2.1)
  case lc_app t1 t2 lct1 lct2 ih1 ih2 =>
    intro Γ T1 T2 ty1 ty2
    cases ty1
    next S1 sy1 sy2 =>
      cases ty2
      next U1 uy1 uy2 =>
        have this := ih1 _ _ _ sy2 uy2
        have this2 := ih2 _ _ _ sy1 uy1
        simp [this2] at this
        exact this

theorem typing_decidable :
    ∀ t Γ, lc t → valid_ctx Γ →
    (∃ T, typing Γ t T) ∨ ¬ (∃ T, typing Γ t T) := by
  intro t Γ lct vld
  induction lct generalizing Γ
  case lc_var x =>
    match h : (get x Γ) with
    | some T =>
        left
        use T
        apply typ_var Γ x T vld h
    | none =>
        right
        rintro ⟨T, typ⟩
        cases typ
        next _ ih =>
          simp [h] at ih
  case lc_abs u T L a ih =>
    have ⟨x,hx⟩ := pick_fresh u (L ∪ context_terms Γ)
    simp at hx
    cases H : (ih x hx.1 ((x,T) :: Γ)
        (valid_push Γ x T vld (not_context_terms_to_not_in_context _ _ hx.2.1)))
    next pos =>
      rcases pos with ⟨S, p⟩
      left
      use (T -> S)
      apply (typ_abs (fv u ∪ context_terms Γ) Γ)
      intro y hy
      simp at hy
      apply typing_rename _ _ _ _ _ _
              hx.2.2 (not_context_terms_to_not_in_context _ _ hx.2.1)
              hy.1 ((not_context_terms_to_not_in_context _ _ hy.2)) p
    next neg =>
      right
      rintro ⟨S,p⟩
      cases p
      next L' S' h =>
        have ⟨z,hz⟩ := pick_fresh u (L' ∪ context_terms Γ)
        simp at hz
        apply neg
        use S'
        apply typing_rename _ _ _ _ _ _
                hz.2.2 ((not_context_terms_to_not_in_context _ _ hz.2.1))
                hx.2.2 ((not_context_terms_to_not_in_context _ _ hx.2.1)) (h z hz.1)
  case lc_app t1 t2 lc1 lc2 ih1 ih2 =>
    cases (ih1 Γ vld)
    next pos =>
      rcases pos with ⟨T,p1⟩
      cases (ih2 Γ vld)
      next pos2 =>
        rcases pos2 with ⟨S,p2⟩
        match T with
        | typ_base =>
          right
          rintro ⟨T, P⟩
          cases P
          next S ty1 ty2 =>
            have q:= typing_unique _ lc1 _ _ _ p1 ty2
            simp at (q)
        | typ_arrow S1 S2 =>
          by_cases h : S1 = S
          . left
            use S2
            rw [← h] at p2
            apply typ_app Γ t1 t2 S1 S2 p1 p2
          . right
            rintro ⟨U, P⟩
            cases P
            next V ty1 ty2 =>
              have q := typing_unique _ lc1 _ _ _ p1 ty2
              simp at q
              have q' := typing_unique _ lc2 _ _ _ p2 ty1
              rw [← q'] at q
              apply (h q.1)
      next neg2 =>
        right
        rintro ⟨T, P⟩
        cases P
        next T1 ty1 ty2 =>
          apply neg2 ⟨_ , ty1⟩
    next neg =>
      right
      rintro ⟨T, P⟩
      cases P
      next T1 ty1 ty2 =>
        apply neg ⟨_ , ty2⟩

theorem typechecking_decidable t T Γ :
    lc t → valid_ctx Γ → (typing Γ t T) ∨ ¬(typing Γ t T) := by
  intro lct vld
  have this := typing_decidable t Γ lct vld
  cases this
  next pos =>
    rcases pos with ⟨S, P⟩
    by_cases h : S = T
    . rw [h] at P
      exact (Or.inl P)
    . right
      intro Q
      have q := typing_unique _ lct _ _ _ P Q
      exact h q
  next neg =>
    right
    simp at neg
    exact neg T

end Lp2lc.Active.STLC
