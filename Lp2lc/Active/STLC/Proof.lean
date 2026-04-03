import «Lp2lc».Active.STLC.Def


namespace Lp2lc.Active.STLC

-- Basic types --
namespace Trm

-- Notations --
lemma pick_fresh (t : Trm) (L : Finset Var) : ∃ (x : Var), x ∉ (L ∪ fv t) := by
  simpa using (var_fresh (L ∪ fv t))

-- If a variable does not appear free in a term, then substituting for it has no effect --
lemma subst_fresh (t u : Trm) (y : Var) (h : y ∉ (fv t)) : ([y // u] t) = t := by
  induction t
  case bvar i =>
    rfl
  case fvar x =>
    simp only [subst]
    rw [if_neg]
    simp [fv] at h
    exact (fun p => h (p.symm))
  case abs T t ht =>
    simp only [subst, abs.injEq]
    constructor
    simp only
    exact (ht h)
  case app t1 t2 h1 h2 =>
    simp only [subst, app.injEq]
    simp [fv] at h
    exact ⟨(h1 h.1), (h2 h.2)⟩

end Trm


/-
In order to make typing judgments, we need the notion of Env.
The definition is designed to talk about "(x : T)"-like assumptions.
-/

lemma context_terms_iff_in_list (x : Var) (Γ : Env) :
    (x ∈ Env.terms Γ) ↔ Env.in_context x Γ := by
  induction Γ
  case nil =>
    simp only [Env.terms, Finset.notMem_empty, Env.in_context]
  case cons b Γ' f =>
    simp only [Env.terms, Finset.mem_union, Finset.mem_singleton, Env.in_context]
    rw [f]

lemma not_context_terms_to_not_in_context x Γ :
    ¬ (x ∈ Env.terms Γ) →  ¬ Env.in_context x Γ := by
  rw [context_terms_iff_in_list]
  simp

lemma in_context_append_neg (x : Var) (Γ Δ : Env) :
    ¬ (Env.in_context x (Γ ++ Δ)) → ¬ (Env.in_context x Γ) ∧ ¬ (Env.in_context x Δ) := by
  intro H
  induction Γ
  case nil =>
    simp only [Env.in_context, not_false_eq_true, true_and] at H ⊢
    rwa [List.nil_append] at H
  case cons b Γ' f =>
    simp [Env.in_context] at H f ⊢
    exact ⟨⟨H.1, (f (H.2)).1⟩, (f (H.2)).2⟩

lemma in_context_append_neg' (x : Var) (Γ Δ : Env) :
    ¬ (Env.in_context x Γ) ∧ ¬ (Env.in_context x Δ) → ¬ (Env.in_context x (Γ ++ Δ)) := by
  rintro ⟨H1, H2⟩
  induction Γ
  case nil =>
    simp only [List.nil_append]
    exact H2
  case cons b Γ' f =>
    simp [Env.in_context, List.append_eq] at H1 ⊢
    exact ⟨H1.1, f H1.2⟩

-- We can only bind variable once per Env --

--Properties of valid contexts
lemma valid_push (Γ : Env) (x : Var) (T : Typ) :
    Env.valid_ctx Γ → ¬ (Env.in_context x Γ) → Env.valid_ctx ((([(x, T)] : Env) ++ Γ)) := by
  simp only [List.singleton_append]
  exact (Env.valid_ctx.valid_cons Γ x T)

lemma valid_remove_mid (Γ Δ Ψ : Env) :
    Env.valid_ctx (Ψ ++ Δ ++ Γ) -> Env.valid_ctx (Ψ ++ Γ) := by
  induction Ψ
  case nil =>
    induction Δ
    case nil =>
      simp only [List.append_nil, List.nil_append, imp_self]
    case cons b Δ' f =>
      simp only [List.nil_append, List.cons_append] at f ⊢
      intro H
      cases H
      next x S p p' =>
        exact (f p)
  case cons b Ψ f =>
    simp only [List.cons_append, List.append_assoc]
    intro H
    cases H
    next x S p p' =>
      simp only [List.cons_append, List.append_assoc] at f p ⊢
      apply Env.valid_ctx.valid_cons
      exact (f p)
      apply in_context_append_neg'
      constructor
      exact (in_context_append_neg _ _ _ p').1
      exact (in_context_append_neg _ _ _ (in_context_append_neg _ _ _ p').2).2

lemma valid_remove_mid_cons (x : Var) (T : Typ) (Γ Δ : Env) :
    Env.valid_ctx (Δ ++ (x, T ) :: Γ)
    → Env.valid_ctx (Δ ++ Γ) := by
  intro H
  simp only [List.append_cons Δ (x, T ) Γ] at H
  apply valid_remove_mid
  exact H

lemma valid_remove_cons (x : Var) (T : Typ) (Γ : Env) :
    Env.valid_ctx ((x, T ) :: Γ)
    → Env.valid_ctx (Γ) := by
  intro H
  rw [← List.nil_append Γ]
  apply valid_remove_mid_cons
  simp
  exact H

--Extracting (x : T) from a Env
lemma binds_singleton (x : Var) (T : Typ) : Env.binds x T (([(x, T)] : Env)) := by
  simp only [Env.binds]
  simp only [Env.get]
  simp only [ite_true]

lemma binds_singleton_tail (x : Var) (T : Typ) (Γ : Env) :
    Env.binds x T ((([(x, T)] : Env) ++ Γ)) := by
  simp [Env.binds, Env.get, List.append_eq, List.nil_append, ite_true]

lemma binds_tail (x : Var) (T : Typ) (Γ Δ : Env) :
    Env.binds x T Γ → (¬ (Env.in_context x Δ)) → Env.binds x T (Δ ++ Γ) := by
  intro bx nx
  simp [Env.binds] at bx ⊢
  induction Δ
  case nil =>
    simp only [List.nil_append, bx]
  case cons b Δ' f' =>
    simp [Env.in_context] at nx
    push Not at nx
    simp [Env.get, List.append_eq]
    rw [if_neg nx.1]
    apply (f' nx.2)

lemma binds_head (x : Var) (T : Typ) (Γ Δ : Env) :
    Env.binds x T Γ → Env.binds x T (Γ ++ Δ) := by
  induction Γ
  case nil =>
    simp
  case cons b Γ' f =>
    simp only [Env.binds, Env.get, List.append_eq]
    by_cases hxb : x = b.1
    . simp only [List.cons_append, Env.get]
      rw [if_pos hxb, if_pos hxb]
      exact id
    . simp only [List.cons_append, Env.get]
      rw [if_neg hxb]
      intro H
      simp [Env.binds] at f
      rw [if_neg hxb]
      exact (f H)

--Case analysis on Env.binds
lemma binds_concat_inv' (x : Var) (T : Typ) (Γ Δ : Env) :
    Env.binds x T (Γ ++ Δ)
    → ((Env.in_context x Γ) ∨ ¬(Env.binds x T Δ))
    → (Env.binds x T Γ) := by
  induction Γ
  case nil =>
    simp
  case cons b Γ' f =>
    intro bxT h
    rcases h with h1 | h2
    . by_cases hxb : x = b.1
      . simp [if_pos hxb] at bxT ⊢
        exact bxT
      . simp [if_neg hxb] at bxT ⊢
        apply f
        exact bxT
        simp [Env.in_context, hxb] at h1
        left
        exact h1
    . simp only [Env.binds, Env.get]
      by_cases hxb : x = b.1
      . simp [if_pos hxb] at bxT ⊢
        exact bxT
      . simp [if_neg hxb] at bxT ⊢
        apply f
        exact bxT
        right
        exact h2

lemma binds_concat_inv (x : Var) (T : Typ) (Γ Δ : Env) :
    Env.binds x T (Γ ++ Δ)
    → ((¬ (Env.in_context x Γ)) ∧ (Env.binds x T Δ)) ∨ (Env.binds x T Γ) := by
  intro bxT
  refine Iff.mpr or_iff_not_imp_left ?_
  intro H
  apply binds_concat_inv' _ _ _ _ bxT
  push Not at H
  exact Iff.mpr or_iff_not_imp_left H

lemma binds_singleton_inv (x y : Var) (X Y : Typ) :
    Env.binds x X (([(y, Y)] : Env)) → (x = y) ∧ (X = Y) := by
  simp only [Env.binds, Env.get]
  intro H
  by_cases hxy : x = y
  . simp [if_pos hxy] at H
    exact ⟨hxy, H.symm⟩
  . simp [if_neg hxy] at H

lemma binds_mid (x : Var) (T : Typ) (Δ Γ : Env) :
    Env.valid_ctx (Γ ++ (([(x, T)] : Env)) ++ Δ)
    → Env.binds x T (Γ ++ (([(x, T)] : Env)) ++ Δ) := by
  induction Γ
  case nil =>
    simp only [List.nil_append, List.singleton_append, Env.binds, Env.get, List.append_eq, ite_true, implies_true]
  case cons b Γ' f =>
    intro H
    cases H
    next y S H' g =>
      simp only [Env.binds, Env.get, List.append_eq, List.append_assoc, List.singleton_append] at f H' g ⊢
      by_cases hxy : x = y
      . simp [if_pos hxy]
        have ⟨_, t2⟩ := in_context_append_neg _ _ _ g
        simp at t2
        push Not at t2
        by_contra _
        exact (t2.1 hxy.symm)
      . simp [if_neg hxy]
        exact (f H')

lemma binds_mid_eq (x : Var) (T S : Typ) (Γ Δ : Env) :
    Env.binds x T (Δ ++ (([(x, S)] : Env)) ++ Γ)
    → Env.valid_ctx (Δ ++ (([(x, S)] : Env)) ++ Γ) →  T = S := by
  induction Δ
  case nil =>
    simp only [Env.binds, Env.get, List.append_eq, List.nil_append, ite_true, Option.some.injEq, List.singleton_append]
    exact (fun p _ => p.symm)
  case cons b Δ' f =>
    intro p H
    cases H
    next y S' H' g =>
      simp only [Env.binds, Env.get, List.append_eq, List.append_assoc, List.singleton_append] at p f H' g ⊢
      by_cases hxy : x = y
      . have ⟨_, t2⟩ := in_context_append_neg _ _ _ g
        simp at t2
        push Not at t2
        by_contra _
        exact (t2.1 hxy.symm)
      . simp [if_neg hxy] at p
        exact (f p H')

lemma binds_mid_eq_cons (x : Var) (T S : Typ) (Γ Δ : Env) :
    Env.binds x T (Δ ++ (x, S ) :: Γ)
    → Env.valid_ctx (Δ ++ (x, S ) :: Γ) → T = S := by
  intro p H
  simp only [List.append_cons Δ (x, S ) Γ] at p H
  exact (binds_mid_eq x T S Γ Δ p H)

--Additional properties of Env.binds
lemma binds_in_context (x : Var) (T : Typ) (Γ : Env) :
    Env.binds x T Γ → Env.in_context x Γ := by
  induction Γ
  case nil =>
    simp
  case cons b Γ' f =>
    simp only [Env.binds, Env.get, Env.in_context] at f ⊢
    by_cases hxb : x = b.1
    . simp only [if_pos hxb]
      intro _
      exact (Or.inl hxb)
    . simp only [if_neg hxb]
      intro p
      exact (Or.inr (f p))

lemma binds_fresh (x : Var) (T : Typ) (Γ : Env) :
    ¬ Env.in_context x Γ → ¬ Env.binds x T Γ := by
  intro hxin hb
  exact hxin (binds_in_context x T Γ hb)

lemma binds_concat_ok (x : Var) (T : Typ) (Γ Δ : Env) :
    Env.binds x T Γ -> Env.valid_ctx (Δ ++ Γ) -> Env.binds x T (Δ ++ Γ) := by
  induction Δ
  case nil =>
    simp only [Env.binds, List.nil_append]
    exact (fun p _ => p)
  case cons b Δ' f =>
    intro p H
    cases H
    next y S H' g =>
      simp only [Env.binds, Env.get, List.append_eq] at H' ⊢
      by_cases hxy : x = y
      . simp [if_pos hxy]
        by_contra
        apply g
        apply binds_in_context y T (Δ' ++ Γ)
        rw [← hxy]
        exact (f p H')
      . simp [if_neg hxy]
        exact (f p H')

lemma binds_weaken (x : Var) (T : Typ) (Γ Δ Ψ: Env) :
    Env.binds x T (Ψ ++ Γ)
    → Env.valid_ctx (Ψ ++ Δ ++ Γ)
    → Env.binds x T (Ψ ++ Δ ++ Γ) := by
  induction Ψ
  case nil =>
    simp only [Env.binds, List.nil_append]
    exact (fun p H => (binds_concat_ok _ _ _ _ p H))
  case cons b Ψ' f =>
    intro p H
    cases H
    next y S H' g =>
      simp only [Env.binds, Env.get, List.append_eq, List.append_assoc, Env.in_context] at f H' p g ⊢
      by_cases hxy : x = y
      . simp [if_pos hxy] at p ⊢
        exact p
      . simp [if_neg hxy] at p ⊢
        exact (f p H')

lemma binds_weaken_at_head (x : Var) (T : Typ) (Γ Δ : Env) :
    Env.binds x T Δ → Env.valid_ctx (Γ ++ Δ)
    → Env.binds x T (Γ ++ Δ) := (binds_weaken x T Δ Γ [])

lemma binds_remove_mid (x y : Var) (T S : Typ) (Γ Δ : Env) :
    Env.binds x T (Γ ++ ((([(y, S)] : Env)) ++ Δ))
    → x ≠ y → Env.binds x T (Γ ++ Δ) := by
  intro p H
  have t := (binds_concat_inv x T Γ ((([(y, S)] : Env)) ++ Δ) p)
  rcases t with ⟨t11, t12⟩ | t2
  . apply (binds_tail x T Δ Γ)
    simp [if_neg H] at t12
    exact t12
    exact t11
  . apply (binds_head _ _ _ _ t2)

lemma binds_remove_mid_cons  (x y : Var) (T S : Typ) (Γ Δ : Env) :
    Env.binds x T (Δ ++ (y, S ) :: Γ)
    → x ≠ y → Env.binds x T (Δ ++ Γ) := by
  intro H p
  apply (binds_remove_mid x y T S Δ Γ)
  rwa [List.append_cons, List.append_assoc] at H
  exact p



namespace Trm

/- Variable opening turns some bound variables into free variables.
It is used to investigate the body of an abstraction.
Variable closing turns some free variables into bound variables.
It is used to build an abstraction given a representation of its body. -/

lemma open_var_fv (t u: Trm) :
    (k : Nat) → fv (opening k u t) ⊆ (fv t) ∪ (fv u) := by
  induction t
  case bvar i =>
    intro k
    simp [opening]
    by_cases h : k = i
    . rw [if_pos h, fv]
      simp
    . rw [if_neg h, fv]
      simp
  case fvar x =>
    simp [opening, fv]
  case abs T t ht =>
    simp [opening, fv]
    exact (fun k => ht (k + 1))
  case app t1 t2 ht1 ht2 =>
    simp [opening, fv]
    intro k
    apply (@Finset.Subset.trans Var _ ((fv t1 ∪ fv u) ∪ (fv t2 ∪ fv u)) _)
    exact Finset.union_subset_union (ht1 k) (ht2 k)
    simp [Finset.union_assoc]
    refine Finset.union_subset_union_right ?_
    rw [Finset.union_comm]
    simp

lemma opening_lc_lemma (t u v : Trm) :
    (i j: Nat) → i ≠ j
    → ({j ~> u} t) = ({i ~> v} ({j ~> u} t))
    → t = ({i ~> v} t) := by
  induction t
  case bvar k =>
   intro i j neqij h
   by_cases hik : (i = k)
   . have hjk : ¬ j = k := by
       intro hjk
       apply neqij
       rw [hik, hjk]
     simp [opening, hik, hjk] at h ⊢
     exact h
   . simp [opening, hik]
  case fvar y =>
   intro i j _ _
   rfl
  case abs T u hu =>
   intro i j neqij h
   simp [opening] at h
   simp [opening]
   exact ((hu (i + 1) (j + 1) (Iff.mpr Nat.succ_ne_succ_iff neqij)) h)
  case app u1 u2 hu1 hu2 =>
   intro i j neqij h
   simp [opening] at h
   simp [opening]
   constructor
   exact (hu1 i j neqij h.1)
   exact (hu2 i j neqij h.2)

----------------------------------------------------------------------
lemma close_var_fv (t : Trm) (x : Var) :
    (k : Nat) → fv (closing k x t) = (fv t) \ {x} := by
  induction t
  case bvar _ =>
    simp [closing, fv]
  case fvar y =>
    intro k
    simp [closing, fv]
    by_cases hy : x = y
    . rw [if_pos hy, fv, hy]
      simp
    . rw [if_neg hy]
      ext z
      by_cases hz : z = y
      . have hyx : y ≠ x := by
          intro h
          exact hy h.symm
        simp [fv, hz, hyx]
      . simp [fv, hz]
  case abs T u hu =>
    intro k
    simp [closing, fv]
    exact (hu (k + 1))
  case app u1 u2 hu1 hu2 =>
    intro k
    simp [closing, fv]
    simp [hu1 k, hu2 k]
    exact Eq.symm (Finset.union_sdiff_distrib (fv u1) (fv u2) {x})

----------------------------------------------------------------------
--Locally closed terms

/-The predicate “body t” asserts that t describes
the body of a locally closed abstraction.-/
lemma lc_abs_iff_body : ∀ t T, lc (abs T t) ↔ body t := by
  intro t T
  constructor
  . intro h
    cases h
    next L a =>
      use L
  . rintro ⟨L, h⟩
    exact (lc.lc_abs t T L h)
----------------------------------------------------------------------
/-The following lemmas show that opening and closing
are inverses of each other on variables.-/
--1) Close(Open)=Id
lemma close_open (x : Var) (t : Trm) :
    x ∉ fv t → (k : Nat) → closing k x (opening k ($ x) t) = t := by
  intro hx
  induction t
  case bvar i =>
    intro j
    simp [opening, closing]
    by_cases hi : j = i
    . rw [if_pos]
      simp only [closing, ite_true, bvar.injEq, hi]
      exact hi
    . rw [if_neg]
      simp only [closing]
      exact hi
  case fvar y =>
    simp [opening, closing]
    simp [fv] at hx
    exact hx
  case abs u hu =>
    simp [opening, closing] at hu ⊢
    rw [fv] at hx
    exact (fun p => hu hx (p + 1))
  case app u1 u2 hu1 hu2 =>
    simp [opening, closing]
    simp [fv] at hx
    exact (fun p => ⟨hu1 hx.1 p, hu2 hx.2 p⟩)

--special case of close_open at j=0
lemma close_open_var (x : Var) (t : Trm) :
    x ∉ fv t → close₀ (open₀ t ($ x)) x = t := fun hx => close_open x t hx 0

--Using this fact, we can show open₀ is injective on terms.
lemma open₀_injective (x : Var) (t1 t2 : Trm) :
    x ∉ fv t1 → x ∉ fv t2 → open₀ t1 ($ x) = open₀ t2 ($ x) → t1 = t2 := by
  intro hx1 hx2 eq
  rw [← close_open_var x t1 hx1]
  rw [← close_open_var x t2 hx2]
  rw [eq]

----------------------------------------------------------------------
--2) Open(Close)=Id
--First, we need a lemma.
lemma open_close_lemma (x y z : Var) (t : Trm) : x ≠ y → y ∉ fv t
    → ((i j : Nat) → i ≠ j → ({ i ~> ($ y)} ({j ~> ($ z)} ({j <~ x} t)))
      = ({j ~> ($ z)} ({j <~ x} ({i ~> ($ y)} t))) ):= by
  intro neqxy hy
  induction t
  case bvar k =>
    intro i j neqij
    simp only [opening]
    by_cases hik : i = k
    . simp only [closing, opening]
      rw [if_pos hik]
      rw [if_neg]
      simp only [opening, closing]
      rw [if_pos hik, if_neg neqxy, opening]
      exact (fun p => neqij (by rw [← p] at hik; exact hik))
    . rw [if_neg hik]
      simp [opening]
      by_cases hjk : j = k
      . rw [if_pos hjk]
        simp only [opening]
      . rw [if_neg hjk]
        simp only [opening, ite_eq_right_iff]
        intro ik
        simp
        exact (hik ik)
  case fvar a =>
    intro i j _
    simp only [closing]
    by_cases hxa : x = a
    . simp only [opening, closing]
      rw [if_pos hxa]
      simp only [opening, ite_true]
    . simp only [opening, closing]
      rw [if_neg hxa]
      simp only [opening]
  case abs T u hu =>
    simp only [ne_eq, opening, abs.injEq]
    rw [fv] at hy
    intro i j neqij
    simp only [closing, opening, abs.injEq]
    constructor
    simp only
    apply (hu hy (i + 1) (j + 1))
    exact Iff.mpr Nat.succ_ne_succ_iff neqij
  case app u1 u2 hu1 hu2 =>
    intro i j neqij
    simp only [closing, opening, app.injEq]
    simp [fv] at hy
    exact ⟨hu1 hy.1 i j neqij, hu2 hy.2 i j neqij⟩

lemma open_close (x : Var) (t : Trm) :
    lc t → (k : Nat) → opening k ($ x) (closing k x t) = t := by
  intro lct
  induction lct
  case lc_var y =>
    intro j
    simp [closing]
    by_cases hxy : x = y
    . rw [if_pos, hxy]
      simp [closing]
      exact hxy
    . rw [if_neg]
      simp [closing]
      exact hxy
  case lc_abs u T L _ hu =>
    intro j
    simp [closing, opening]
    let ⟨y, hy⟩ := pick_fresh u (L ∪ (fv ($ x)) ∪ (fv (( {j + 1 ~> $ x} { j + 1 <~ x } u))))
    simp at hy
    apply (open₀_injective y ( {j + 1 ~> $ x} { j + 1 <~ x } u)  u (hy.2.2.1) (hy.2.2.2))
    rw [← (hu y (hy.1) (j + 1))]
    simp [open₀]
    apply (open_close_lemma x y x u)
    have hyx := hy.2.1
    simp [fv] at hyx
    exact (fun p => hyx p.symm)
    exact hy.2.2.2
    exact (Nat.succ_ne_zero j).symm
  case lc_app u1 u2 _ _ hu1 hu2 =>
    intro j
    simp [opening, closing]
    exact ⟨hu1 j, hu2 j⟩

--special case of open_close at j=0
lemma open_close_var (x : Var) (t : Trm) :
    lc t → open₀ (close₀ t x) ($ x) = t := by
  intro lct
  exact (open_close x t lct 0)

--Using this fact, we can show closing is injective on terms.
lemma closing_injective (x : Var) (i : Nat) (t1 t2 : Trm) :
    lc t1 → lc t2 → closing i x t1 = closing i x t2 → t1 = t2 := by
  intro lct1 lct2 eq
  rw [← open_close x t1 lct1 i]
  rw [← open_close x t2 lct2 i]
  rw [eq]

-----------------------------------------
--Auxilary lemma about opening
lemma opening_lc (t u : Trm) : lc t → (k : Nat) → (t = {k ~> u} t) := by
  intro lce
  induction lce
  case lc_var x =>
    intro _
    rfl
  case lc_abs v T L _ hv =>
    intro i
    simp [open₀] at hv
    rw [opening]
    have ⟨x, hx0⟩ := pick_fresh u L
    have hx : x ∉ L := by
      exact (Finset.notMem_union.mp hx0).1
    have h : v = { i + 1 ~> u } v := by
      apply (opening_lc_lemma v ($ x) u (i + 1) 0)
      exact Nat.succ_ne_zero i
      exact (hv x hx (i + 1))
    rw [← h]
  case lc_app u1 u2 _ _ hu1 hu2 =>
    intro i
    simp [opening]
    exact ⟨hu1 i, hu2 i⟩

lemma open₀_lc (t u : Trm) : lc t → (t = open₀ t u) := by
  intro lce
  simp [open₀]
  apply (opening_lc t u lce 0)

--Free variable substitution distributes over index substitution.
lemma subst_open_rec (t1 t2 u : Trm) : (i : Var) → (j : Nat) → lc u
    → ([i // u] ({j ~> t2} t1)) = ({j ~> [i // u] t2} ([i // u] t1)) := by
  induction t1
  case bvar k =>
   intro i j _
   by_cases hjk : (j = k)
   . simp [opening]
     rw [if_pos, if_pos] <;> exact hjk
   . simp [opening]
     rw [if_neg, if_neg, subst]
     <;> exact hjk
  case fvar y =>
   intro i j lcu
   by_cases hyi : (y = i)
   . simp [opening, subst]
     rw [if_pos]
     exact (opening_lc u ([ i // u ] t2) lcu j)
     exact hyi
   . simp [opening, subst]
     rw [if_neg]
     exact (opening_lc ($ y) ([ i // u ] t2) (lc.lc_var y) j)
     exact hyi
  case abs T v hv =>
   intro i j lcu
   simp [opening, subst]
   exact (hv i (j + 1) lcu)
  case app u1 u2 hu1 hu2 =>
   intro i j lcu
   simp [opening, subst]
   exact ⟨hu1 i j lcu, hu2 i j lcu⟩

--The lemma above is most often used with k = 0 and e2 as some fresh variable.
--Therefore, it simplifies matters to define the following useful corollary.
lemma subst_open_var (t u : Trm) : lc u → (i j : Var) → i ≠ j
    → (open₀ ([i // u] t) ($ j)) = ([i // u] (open₀ t ($ j))) := by
  intro lcu i j neqij
  simp [open₀]
  rw [subst_open_rec t ($ j) u i 0 lcu]
  rw [subst, if_neg]
  exact (fun p => neqij (Eq.symm p))


--When we open a term, we can instead open the term with a fresh variable and
--then substitute for that variable.
lemma subst_intro (t u : Trm) : lc u → (x : Var) → x ∉ (fv t)
    → (open₀ t u) = ([x // u] (open₀ t ($ x))) := by
  intro lcu x hx
  simp [open₀]
  rw [subst_open_rec t ($ x) u x 0 lcu]
  rw [subst, if_pos]
  rw [subst_fresh]
  exact hx
  rfl

lemma subst_lc (t u : Trm) : (x : Var) → lc t → lc u → lc ([x // u] t) := by
  intro x lct lcu
  induction lct
  case lc_var y =>
    rw [subst]
    by_cases hxy : y = x
    . rw [if_pos]
      exact lcu
      exact hxy
    . rw [if_neg]
      exact (lc.lc_var y)
      exact hxy
  case lc_abs v T L _ hv =>
    apply (lc.lc_abs ([ x // u ] v) T (L ∪ {x}))
    intro x₀ hx₀
    have t1 : x₀ ∉ L := by
      intro s
      exact (hx₀ (Finset.mem_union_left {x} s))
    have t2 : x₀ ≠ x := by
      simp at hx₀
      push Not at hx₀
      exact hx₀.1
    rw [subst_open_var v u lcu x x₀ t2.symm]
    exact (hv x₀ t1)
  case lc_app t1 t2 lct1 lct2 ht1 ht2 =>
    dsimp [subst]
    apply (lc.lc_app ( [ x // u ] t1) ( [ x // u ] t2) ht1 ht2)

lemma open_var_body : ∀ x t, body t → lc (open₀ t ($ x)) := by
  intro x t bt
  rcases bt with ⟨L , a⟩
  have ⟨y, hy⟩ := pick_fresh t (L ∪ {x})
  simp at hy
  push Not at hy
  rw [subst_intro t ($ x) (lc.lc_var x) y (hy.2.2)]
  apply (subst_lc (open₀ t ($ y)) ($ x))
  exact (a y hy.2.1)
  exact (lc.lc_var x)

lemma open_var_lc : ∀ x t, lc (abs T t) → lc (open₀ t ($ x)) := by
  intro x t lcat
  rw [lc_abs_iff_body t] at lcat
  exact (open_var_body x t lcat)

lemma open_body : ∀ t u, body t → lc u → lc (open₀ t u) := by
  intro t u bt lcu
  rcases bt with ⟨L , a⟩
  have ⟨y, hy⟩ := pick_fresh t L
  simp at hy
  rw [subst_intro t u lcu y hy.2]
  exact (subst_lc (open₀ t ($ y)) u y (a y hy.1) lcu)

--general version of open_var_lc
lemma open_lc : ∀ t u, lc (abs T t) → lc u → lc (open₀ t u) := by
  intro t u lcat lcu
  rw [lc_abs_iff_body t] at lcat
  exact (open_body t u lcat lcu)

lemma open_close_subst t x y :
    lc t → (∀ k, (opening k ($ y) (closing k x t)) = ([x // ($ y)] t)) := by
  intro lct
  induction lct
  case lc_var y =>
    simp only [closing, subst]
    by_cases hxy : x = y
    . simp [if_pos hxy, if_pos hxy.symm]
    . have hyx : y ≠ x := (fun p => (hxy p.symm))
      simp [if_neg hxy, if_neg hyx]
  case lc_abs s T L f h =>
    simp [opening, subst, abs.injEq]
    intro k
    let ⟨w, qw⟩ := pick_fresh s (L ∪ {x} ∪ (fv ( {k + 1 ~> $ y} { k + 1 <~ x } s)) ∪ (fv ([x // $ y] s)))
    simp at qw
    push Not at qw
    have hwx : x ≠ w := (fun p => (qw.1 p.symm))
    have fact := h w qw.2.1 (k + 1)
    rw [← subst_open_var _ _ (lc.lc_var y) _ _ hwx, open₀] at fact
    rw [← open_close_lemma _ _ _ _ hwx, ← open₀] at fact
    apply open₀_injective w _
    exact qw.2.2.1
    exact qw.2.2.2.1
    exact fact
    exact qw.2.2.2.2
    exact Nat.ne_of_beq_eq_false rfl
  case lc_app u1 u2 _ _ f1 f2 =>
    intro k
    simp
    exact ⟨f1 k, f2 k⟩

end Trm



/- # Different Forms of β-reductions -/

--full beta reduction

lemma beta_red_regular : ∀ t1 t2, (beta_red t1 t2) → (Trm.lc t1) ∧ (Trm.lc t2) := by
  intro t1 t2 t1rt2
  induction t1rt2
  case br_beta s1 s2 T lcas1 lcs2 =>
    constructor
    exact (Trm.lc.lc_app (Trm.abs T s1) s2 lcas1 lcs2)
    exact (Trm.open_lc s1 s2 lcas1 lcs2)
  case br_app1 s1 s1' s2 lcs2 _ h =>
    exact ⟨Trm.lc.lc_app s1 s2 h.1 lcs2, Trm.lc.lc_app s1' s2 h.2 lcs2⟩
  case br_app2 s1 s2 s2' lcs1 _ h =>
    exact ⟨Trm.lc.lc_app s1 s2 lcs1 h.1, Trm.lc.lc_app s1 s2' lcs1 h.2⟩
  case br_abs s1 s1' T L _ h =>
    constructor
    . apply (Trm.lc.lc_abs s1 T L (fun x hx => (h x hx).1))
    . apply (Trm.lc.lc_abs s1' T L (fun x hx => (h x hx).2))

lemma beta_rename t1 t2 x y : beta_red t1 t2
    → beta_red ([x // ($ y)] t1) ([x // ($ y)] t2) := by
  intro R
  induction R
  case br_beta s1 s2 T lc1 lc2 =>
    rw [Trm.open₀]
    rw [Trm.subst_open_rec s1 s2 ($ y) x 0 (Trm.lc.lc_var y)]
    rw [← Trm.open₀]
    apply beta_red.br_beta
    . rw [← Trm.subst]
      apply Trm.subst_lc
      exact lc1
      exact (Trm.lc.lc_var y)
    . apply Trm.subst_lc
      exact lc2
      exact (Trm.lc.lc_var y)
  case br_app1 s1 s1' s2 lc2 bs1' h =>
    simp only [Trm.subst]
    apply beta_red.br_app1
    apply Trm.subst_lc
    apply lc2
    apply (Trm.lc.lc_var)
    exact h
  case br_app2 s1 s2 s2' lc1 bs2' h =>
    simp only [Trm.subst]
    apply beta_red.br_app2
    apply Trm.subst_lc
    apply lc1
    apply (Trm.lc.lc_var)
    exact h
  case br_abs s1 s1' T L h f =>
    simp only [Trm.subst]
    apply beta_red.br_abs _ _ _ (L ∪ {x})
    intro z hz
    simp at hz
    push Not at hz
    simp [Trm.subst_open_var s1 ($ y) (Trm.lc.lc_var y) x z (fun p => hz.1 p.symm)]
    simp [Trm.subst_open_var s1' ($ y) (Trm.lc.lc_var y) x z (fun p => hz.1 p.symm)]
    exact (f z hz.2)

lemma beta_abs_intro t1 t2 T x :
    beta_red (Trm.open₀ t1 ($ x)) (Trm.open₀ t2 ($ x))
    → x ∉ Trm.fv t1 → x ∉ Trm.fv t2 → beta_red (λT, t1) (λT, t2) := by
  intro R fx1 fx2
  apply beta_red.br_abs t1 t2 T ∅
  intro y _
  rw [Trm.subst_intro _ _ _ x fx1, Trm.subst_intro _ _ _ x fx2]
  apply beta_rename
  exact R
  exact (Trm.lc.lc_var y)
  exact (Trm.lc.lc_var y)

lemma beta_red_subst_out t1 t2 x u :
    (beta_red t1 t2) ∧ (Trm.lc u)
    → (beta_red ([x // u] t1) ([x // u] t2)) := by
  rintro ⟨t1bt2, lcu⟩
  induction t1bt2
  case br_beta s1 s2 T lc1 lc2 =>
    simp only [Trm.subst]
    have q : ([x // u] Trm.open₀ s1 s2) = Trm.open₀ ([x // u] s1) ([x // u] s2) := by
      simp [Trm.open₀]
      apply Trm.subst_open_rec
      exact lcu
    rw [q]
    apply beta_red.br_beta
    rw [← Trm.subst]
    apply Trm.subst_lc
    exact lc1
    exact lcu
    apply Trm.subst_lc
    exact lc2
    exact lcu
  case br_app1 s1 s1' s2 lc2 s1bs1' f =>
    simp only [Trm.subst]
    apply beta_red.br_app1
    apply Trm.subst_lc
    exact lc2
    exact lcu
    exact f
  case br_app2 s1 s2 s2' lc1 s2bs2' f =>
    simp only [Trm.subst]
    apply beta_red.br_app2
    apply Trm.subst_lc
    exact lc1
    exact lcu
    exact f
  case br_abs s1 s2 T L f h =>
    simp only [Trm.subst]
    let ⟨y, hy⟩ := Trm.pick_fresh ([x // u] s1) (L ∪ (Trm.fv ([x // u] s2)) ∪ {x})
    apply beta_abs_intro _ _ _ y
    simp at hy
    push Not at hy
    rw [Trm.subst_open_var _ _ lcu , Trm.subst_open_var _ _ lcu]
    apply (h y hy.2.1)
    exact (fun p => hy.1 p.symm)
    exact (fun p => hy.1 p.symm)
    simp at hy
    push Not at hy
    exact hy.2.2.2
    simp at hy
    push Not at hy
    exact hy.2.2.1

-------------------------

--paralel reduction

lemma para_regular : ∀ t1 t2, (para t1 t2) → (Trm.lc t1) ∧ (Trm.lc t2) := by
  intro t1 t2 t1pt2
  induction t1pt2
  case para_var x =>
    exact ⟨Trm.lc.lc_var x, Trm.lc.lc_var x⟩
  case para_red s1 s1' s2 s2' T L _ _ h h' =>
    constructor
    . apply (Trm.lc.lc_app (Trm.abs T s1) s2)
      exact (Trm.lc.lc_abs s1 T L (fun x hx => (h x hx).1))
      exact h'.1
    . apply (Trm.open_lc s1' s2')
      exact (Trm.lc.lc_abs s1' T L (fun x hx => (h x hx).2))
      exact h'.2
  case para_app s1 s1' s2 s2' _ _ h1 h2 =>
    exact ⟨Trm.lc.lc_app s1 s2 h1.1 h2.1, Trm.lc.lc_app s1' s2' h1.2 h2.2⟩
  case para_abs s1 s1' T L _ h =>
    constructor
    . exact (Trm.lc.lc_abs s1 T L (fun x hx => (h x hx).1))
    . exact (Trm.lc.lc_abs s1' T L (fun x hx => (h x hx).2))

lemma lc_para_refl : ∀ t, Trm.lc t → para t t := by
  intro t lct
  induction lct
  case lc_var x =>
    exact (para.para_var x)
  case lc_abs u T L _ h =>
    apply (para.para_abs u u T L)
    exact h
  case lc_app u1 u2 _ _ h h' =>
    exact (para.para_app u1 u1 u2 u2 h h')

lemma para_subst_all t1 t2 s1 s2 :
    (para t1 t2) → (para s1 s2)
    → ∀ x, (para ([x // s1] t1) ([x // s2] t2)) := by
  intro t1pt2 s1ps2 x
  induction t1pt2
  case para_var y =>
    simp only [Trm.subst]
    by_cases hyx : y = x
    . simp only [if_pos hyx]
      exact s1ps2
    . simp only [if_neg hyx]
      exact (para.para_var y)
  case para_red u1 u1' u2 u2' T L f u2pu2' g h =>
    simp only [Trm.subst]
    rw [Trm.open₀, (Trm.subst_open_rec u1' u2' s2 x 0 (para_regular _ _ s1ps2).2), ← Trm.open₀]
    apply para.para_red _ _ _ _ _ (L ∪ {x})
    intro y hy
    simp at hy
    push Not at hy
    have p : x ≠ y := (fun q => (hy.1 q.symm))
    rw [Trm.subst_open_var u1 s1 (para_regular _ _ s1ps2).1 x y p]
    rw [Trm.subst_open_var u1' s2 (para_regular _ _ s1ps2).2 x y p]
    exact (g y hy.2)
    exact h
  case para_app u1 u1' u2 u2' u1pu1' u2pu2' f g =>
    simp only [Trm.subst]
    apply para.para_app
    exact f
    exact g
  case para_abs u1 u1' T L f g =>
    simp only [Trm.subst] at g ⊢
    apply para.para_abs _ _ _ (L ∪ {x})
    intro y hy
    simp at hy
    push Not at hy
    have p : x ≠ y := (fun q => (hy.1 q.symm))
    rw [Trm.subst_open_var _ _ _ x y p, Trm.subst_open_var _ _ _ x y p]
    exact (g y hy.2)
    exact (para_regular _ _ s1ps2).2
    exact (para_regular _ _ s1ps2).1

lemma para_open_out t t' u u' (L : Finset Var) :
    (∀ x, x ∉ L → para (Trm.open₀ t ($ x)) (Trm.open₀ u ($ x)))
    → para t' u' → para (Trm.open₀ t t') (Trm.open₀ u u') := by
  intro f tpu'
  let ⟨x, qx⟩ := Trm.pick_fresh t (L ∪ (Trm.fv u))
  simp at qx
  rw [Trm.subst_intro t t' (para_regular _ _ tpu').1 x qx.2.2]
  rw [Trm.subst_intro u u' (para_regular _ _ tpu').2 x qx.2.1]
  apply para_subst_all
  exact (f x qx.1)
  exact tpu'

lemma opening_closing_para t u x y z :
    para t u → y ∉ ((Trm.fv t) ∪ (Trm.fv u) ∪ {x})
    → para (Trm.opening z ($ y) (Trm.closing z x t))
           (Trm.opening z ($ y) (Trm.closing z x u)) := by
  intro tpu hy
  simp at hy
  push Not at hy
  rw [Trm.open_close_subst t x y (para_regular _ _ tpu).1 z]
  rw [Trm.open_close_subst u x y (para_regular _ _ tpu).2 z]
  apply para_subst_all _ _ _ _ tpu (para.para_var y)

lemma open_close_para t u x y :
    para t u → y ∉ ((Trm.fv t) ∪ (Trm.fv u) ∪ {x})
    → para (Trm.open₀ (Trm.close₀ t x) ($ y))
           (Trm.open₀ (Trm.close₀ u x) ($ y)) := opening_closing_para t u x y 0

lemma para_through t1 t2 u1 u2 x :
    (x ∉ Trm.fv t1 ∧ x ∉ Trm.fv t2)
    → (para (Trm.open₀ t1 ($ x)) (Trm.open₀ t2 ($ x)))
    → (para u1 u2) → (para (Trm.open₀ t1 u1) (Trm.open₀ t2 u2)) := by
  rintro ⟨h1, h2⟩ f g
  rw [Trm.subst_intro t1 u1 (para_regular _ _ g).1 x h1]
  rw [Trm.subst_intro t2 u2 (para_regular _ _ g).2 x h2]
  apply para_subst_all
  exact f
  exact g

---------------------------
--multiple-step reduction

lemma multi_red_trans t1 t2 t3 :
    (multi_red t1 t2) → (multi_red t2 t3) → (multi_red t1 t3) := by
  intro t1mlt2 t2mlt3
  induction t2mlt3
  case mr_refl _ =>
    exact t1mlt2
  case mr_head s1 s2 _ s2bs3 f =>
    apply multi_red.mr_head
    . exact f
    . exact s2bs3

lemma multi_red_regular :
    ∀ t1 t2, (multi_red t1 t2) → (Trm.lc t1) ∧ (Trm.lc t2) := by
  intro t1 t2 t1mt2
  induction t1mt2
  case mr_refl s =>
    exact ⟨s, s⟩
  case mr_head s1 s2 _ s2bs3 h =>
    exact ⟨h.1, (beta_red_regular s1 s2 s2bs3).2⟩

lemma beta_to_multi_red :
    ∀ t1 t2, (beta_red t1 t2) → (multi_red t1 t2) := by
  intro t1 t2 t1rt2
  apply (multi_red.mr_head t1 t1 t2)
  apply (multi_red.mr_refl t1)
  exact (beta_red_regular t1 t2 t1rt2).1
  exact t1rt2

lemma multi_red_abs_intro' u1 u2 T x :
    multi_red u1 u2
    → (∀ t1 t2, u1 = Trm.open₀ t1 ($ x) → u2 = Trm.open₀ t2 ($ x)
       → x ∉ Trm.fv t1 → x ∉ Trm.fv t2 → multi_red (λT, t1) (λT, t2)) := by
  intro u1mu2
  induction u1mu2
  case mr_refl t =>
    intro t1 t2 p1 p2 fx1 fx2
    rw [p1] at p2
    have q := Trm.open₀_injective _ _ _ fx1 fx2 p2
    rw [q]
    apply multi_red.mr_refl
    apply Trm.lc.lc_abs t2 T ∅
    intro z _
    rw [Trm.subst_intro t2 ($ z) (Trm.lc.lc_var z) x fx2]
    apply Trm.subst_lc
    rw [← q, ← p1]
    exact t
    exact (Trm.lc.lc_var z)
  case mr_head s1 s2 _ s1bs2 f =>
    intro t1 t2 p1 p2 fx1 fx2
    apply multi_red.mr_head _ (λ T,(Trm.close₀ s1 x)) _
    apply (f t1 (Trm.close₀ s1 x))
    exact p1
    rw [← (Trm.open_close_var x s1 (beta_red_regular _ _ s1bs2).1).symm]
    exact fx1
    simp [Trm.close₀, Trm.close_var_fv s1 x 0]
    apply (beta_abs_intro (Trm.close₀ s1 x) t2)
    rw [← p2]
    rw [← (Trm.open_close_var x s1 (beta_red_regular _ _ s1bs2).1).symm]
    exact s1bs2
    simp [Trm.close₀, Trm.close_var_fv s1 x 0]
    exact fx2

lemma multi_red_abs_intro t1 t2 T x :
    multi_red (Trm.open₀ t1 ($ x)) (Trm.open₀ t2 ($ x))
    → x ∉ Trm.fv t1 → x ∉ Trm.fv t2 → multi_red (λT, t1) (λT, t2) := by
  intro R hx1 hx2
  apply (multi_red_abs_intro' (Trm.open₀ t1 ($ x)) (Trm.open₀ t2 ($ x)) T x)
  exact R
  simp
  simp
  exact hx1
  exact hx2

lemma multi_red_abs t1 t2 T (L : Finset Var):
    (∀ x, x ∉ L → multi_red (Trm.open₀ t1 ($ x)) (Trm.open₀ t2 ($ x)))
    → multi_red (λT, t1) (λT, t2) := by
  intro f
  let ⟨x, hx⟩ := Trm.pick_fresh t2 (L ∪ (Trm.fv t1))
  simp at hx
  apply (multi_red_abs_intro t1 t2 T x)
  apply (f x hx.1)
  exact hx.2.1
  exact hx.2.2

lemma multi_red_app1 t1 t1' t2 :
    (multi_red t1 t1') ∧ (Trm.lc t2)
    → (multi_red (Trm.app t1 t2) (Trm.app t1' t2)) := by
  rintro ⟨t1mt2, lct2⟩
  induction t1mt2
  case mr_refl t =>
    apply multi_red.mr_refl
    apply Trm.lc.lc_app
    exact t
    exact lct2
  case mr_head s1 s2 _ s1bs2 f =>
    apply multi_red.mr_head _ (s1 @ t2) _
    exact f
    apply beta_red.br_app1
    exact lct2
    exact s1bs2

lemma multi_red_app2 t1 t2 t2' :
    (multi_red t2 t2') ∧ (Trm.lc t1)
    → (multi_red (Trm.app t1 t2) (Trm.app t1 t2')) := by
  rintro ⟨t1mt2, lct1⟩
  induction t1mt2
  case mr_refl t =>
    apply multi_red.mr_refl
    apply Trm.lc.lc_app
    exact lct1
    exact t
  case mr_head s1 s2 _ s1bs2 f =>
    apply multi_red.mr_head _ (t1 @ s1) _
    exact f
    apply beta_red.br_app2
    exact lct1
    exact s1bs2

lemma multi_red_subst_in t x u1 u2 :
    (multi_red u1 u2) ∧ (Trm.lc t)
    → (multi_red ([x // u1] t) ([x // u2] t)) := by
  rintro ⟨u1mu2, lct⟩
  induction lct
  case lc_var i =>
    simp only [Trm.subst]
    by_cases hix : i = x
    . simp [if_pos hix]
      exact u1mu2
    . simp [if_neg hix]
      exact (multi_red.mr_refl _ (Trm.lc.lc_var i))
  case lc_abs u T L h f =>
    simp [Trm.subst]
    apply multi_red_abs _ _ _ (L ∪ {x})
    intro y hy
    simp at hy
    push Not at hy
    rw [Trm.subst_open_var u u1 (multi_red_regular _ _ u1mu2).1 x y]
    rw [Trm.subst_open_var u u2 (multi_red_regular _ _ u1mu2).2 x y]
    apply (f y hy.2)
    exact (fun s => hy.1 s.symm)
    exact (fun s => hy.1 s.symm)
  case lc_app s1 s2 lc1 lc2 h1 h2 =>
    simp [Trm.subst]
    apply multi_red_trans _ (([x // u2] s1) @ ([x // u1] s2)) _
    apply multi_red_app1
    constructor
    . apply h1
    . apply Trm.subst_lc
      exact lc2
      apply (multi_red_regular _ _ u1mu2).1
    apply multi_red_app2
    constructor
    . apply h2
    . apply Trm.subst_lc
      apply lc1
      apply (multi_red_regular _ _ u1mu2).2

lemma multi_red_subst_all t1 t2 x u1 u2 :
    (multi_red t1 t2) ∧ (multi_red u1 u2)
    → (multi_red ([x // u1] t1) ([x // u2] t2)) := by
  rintro ⟨t1mt2, u1mu2⟩
  induction t1mt2
  case mr_refl lct =>
    apply multi_red_subst_in
    exact ⟨u1mu2, lct⟩
  case mr_head s1 s2 _ s1bs2 f =>
     apply multi_red.mr_head _ ([x // u2] s1) _
     exact f
     apply beta_red_subst_out
     exact ⟨s1bs2, (multi_red_regular _ _ u1mu2).2⟩

lemma multi_red_through t1 t2 u1 u2 x :
    (x ∉ Trm.fv t1 ∧ x ∉ Trm.fv t2) →
    (multi_red (Trm.open₀ t1 ($ x)) (Trm.open₀ t2 ($ x))) →
    (multi_red u1 u2) →
    (multi_red (Trm.open₀ t1 u1) (Trm.open₀ t2 u2)) := by
  rintro ⟨h1, h2⟩ f g
  rw [Trm.subst_intro t1 u1 (multi_red_regular _ _ g).1 x h1]
  rw [Trm.subst_intro t2 u2 (multi_red_regular _ _ g).2 x h2]
  apply multi_red_subst_all
  exact ⟨f, g⟩

------------------------

--multiple-step paralel reduction

lemma multi_para_trans : ∀ t1 t2 t3,
    (multi_para t1 t2) → (multi_para t2 t3) → (multi_para t1 t3) := by
  intro t1 t2 t3 t1mpt2 t2mpt3
  induction t2mpt3
  case m_para_refl _ =>
   exact t1mpt2
  case m_para_head s1 s2 _ s1ps2 f =>
   apply (multi_para.m_para_head t1 s1 s2)
   exact f
   exact s1ps2

lemma multi_para_regular : ∀ t1 t2, (multi_para t1 t2) → (Trm.lc t1) ∧ (Trm.lc t2) := by
  intro t1 t2 t1mpt2
  induction t1mpt2
  case m_para_refl lct =>
    exact ⟨lct, lct⟩
  case m_para_head s1 s2 _ s1ps2 h =>
    exact ⟨h.1, (para_regular s1 s2 s1ps2).2⟩

lemma para_to_multi_para : ∀ t1 t2, (para t1 t2) → (multi_para t1 t2) := by
  intro t1 t2 t1pt2
  induction t1pt2
  case para_var x =>
    exact (multi_para.m_para_refl ($ x) (Trm.lc.lc_var x))
  case para_red s1 s1' s2 s2' T L f s2ps2' _ b =>
    apply (multi_para.m_para_head _ ((Trm.abs T s1) @ s2) (Trm.open₀ s1' s2'))
    . apply (multi_para.m_para_refl ((Trm.abs T s1) @ s2))
      apply Trm.lc.lc_app
      apply Trm.lc.lc_abs s1 T L
      exact (fun x hx => (para_regular _ _ (f x hx)).1)
      exact (multi_para_regular _ _ b).1
    . apply (para.para_red s1 s1' s2 s2' T L f s2ps2')
  case para_app s1 s1' s2 s2' s1ps1' s2ps2' _ _ =>
    apply multi_para.m_para_head _ (s1 @ s2)
    . apply multi_para.m_para_refl
      apply (Trm.lc.lc_app _ _ (para_regular _ _ s1ps1').1 (para_regular _ _ s2ps2').1)
    . exact (para.para_app s1 s1' s2 s2' s1ps1' s2ps2')
  case para_abs s1 s1' T L f _ =>
    apply (multi_para.m_para_head _ (Trm.abs T s1) (Trm.abs T s1'))
    . apply (multi_para.m_para_refl (Trm.abs T s1))
      apply (Trm.lc.lc_abs s1 T L)
      intro x hx
      exact (para_regular _ _ (f x hx)).1
    . apply (para.para_abs s1 s1' T L f)

------------------------


/- # Equivalence between multi-β reduction and multi-paralel reduction -/

lemma beta_red_to_para : ∀ t t', beta_red t t' → para t t' := by
  intro t t' trt'
  induction trt'
  case br_beta t1 t2 T lcat1 lct2 =>
    apply (para.para_red t1 t1 t2 t2 T ∅)
    simp
    intro x
    exact (lc_para_refl _ (Trm.open_var_lc x t1 lcat1))
    exact (lc_para_refl _ lct2)
  case br_app1 t1 t1' t2 lct2 _ h =>
    apply (para.para_app t1 t1' t2 t2)
    exact h
    exact (lc_para_refl _ lct2)
  case br_app2 t1 t2 t2' lct1 _ h =>
    apply (para.para_app t1 t1 t2 t2')
    exact (lc_para_refl _ lct1)
    exact h
  case br_abs t1 t1' T L _ h =>
    apply (para.para_abs t1 t1' T L)
    exact h

lemma multi_red_to_multi_para : ∀ t t', multi_red t t' → multi_para t t' := by
  intro t t' tmrt'
  induction tmrt'
  case mr_refl lct =>
    exact (multi_para.m_para_refl t lct)
  case mr_head t1 t2 _ t1rt2 t2pt3 =>
    apply multi_para.m_para_head
    exact t2pt3
    exact (beta_red_to_para t1 t2 t1rt2)

lemma para_to_multi_red : ∀ t t', para t t' → multi_red t t' := by
  intro t t' tpt'
  induction tpt'
  case para_var x =>
    exact (multi_red.mr_refl ($ x) (Trm.lc.lc_var x))
  case para_red t1 t1' t2 t2' T L f t2pt2' h h' =>
    apply (multi_red_trans ((Trm.abs T t1) @ t2) (Trm.open₀ t1 t2) (Trm.open₀ t1' t2'))
    . apply (beta_to_multi_red ((Trm.abs T t1) @ t2) (Trm.open₀ t1 t2))
      apply (beta_red.br_beta t1 t2)
      have lcabst1 : Trm.lc (Trm.abs T t1):= by
        apply (Trm.lc.lc_abs t1 T L)
        intro x hx
        have := f x hx
        exact (para_regular (Trm.open₀ t1 ($ x)) (Trm.open₀ t1' ($ x)) (f x hx)).1
      exact lcabst1
      exact (para_regular t2 t2' t2pt2').1
    . have ⟨x, hx⟩ := Trm.pick_fresh t1' (L ∪ Trm.fv t1)
      simp at hx
      apply (multi_red_through t1 t1' t2 t2' x)
      constructor
      .  exact (hx.2).1
      .  exact (hx.2).2
      apply (h x (hx.1))
      exact h'
  case para_app t1 t1' t2 t2' t1pt1' t2pt2' h1 h2 =>
    apply (multi_red_trans (t1 @ t2) (t1' @ t2) (t1' @ t2'))
    . apply (multi_red_app1 t1 t1' t2)
      exact ⟨h1 , (para_regular t2 t2' t2pt2').1⟩
    . apply (multi_red_app2 t1' t2 t2')
      exact ⟨h2 , (para_regular t1 t1' t1pt1').2⟩
  case para_abs t1 t1' T L _ h =>
    apply (multi_red_abs t1 t1' T L h)

lemma multi_para_to_multi_red : ∀ t t', multi_para t t' → multi_red t t' := by
  intro t t' tmpt'
  induction tmpt'
  case m_para_refl lct =>
    exact (multi_red.mr_refl t lct)
  case m_para_head t1 t2 _ t1pt2 t1mlt2 =>
    apply (multi_red_trans t t1 t2)
    exact t1mlt2
    exact (para_to_multi_red t1 t2 t1pt2)

lemma multi_red_iff_multi_para : ∀ t1 t2, (multi_red t1 t2) ↔ (multi_para t1 t2) := by
  intro t1 t2
  constructor
  . exact (multi_red_to_multi_para t1 t2)
  . exact (multi_para_to_multi_red t1 t2)



--Typing judgment

--Typing judgments only allow valid contexts.
lemma typing_valid_ctx  Γ t T : typing Γ t T → Env.valid_ctx Γ := by
  intro H
  induction H
  case typ_var _ _ _ h _ =>
    exact h
  case typ_abs L φ t T1 _ _ f =>
    let ⟨p1, p2⟩ := Trm.pick_fresh t L
    simp at p2
    apply valid_remove_cons
    apply (f p1 p2.1)
  case typ_app _ _ _ _ _ _ _ h1 _ =>
    exact h1
------------------------------------

--Weakining Rule
lemma typing_weakening_strengthened' (Γ Δ Ψ' : Env) (t : Trm) (T : Typ) :
    typing Ψ' t T → (Ψ : Env) → Ψ' = Ψ ++ Γ
    → Env.valid_ctx (Ψ ++ Δ ++ Γ)
    → typing (Ψ ++ Δ ++ Γ) t T := by
  intro H
  induction H
  case typ_var φ x T' _ fT' =>
    intro φ p f
    apply typing.typ_var
    exact f
    rw [p] at fT'
    exact (binds_weaken _ _ _ _ _ fT' f)
  case typ_abs L φ' s T1 T2 _ fT2 =>
    intro φ p f
    apply typing.typ_abs (L ∪ Env.terms (φ ++ Δ ++ Γ))
    intro x hx
    simp at hx
    apply (fT2 x hx.1 ((x, T1) :: φ))
    simp [p]
    apply Env.valid_ctx.valid_cons
    exact f
    simp [List.append_cons]
    intro q
    exact (hx.2 ((context_terms_iff_in_list x _).mpr q))
  case typ_app φ' t1 t2 T1 T2 _ _ fT1 fT2 =>
    intro φ p f
    apply typing.typ_app
    exact (fT1 φ p f)
    exact (fT2 φ p f)

lemma typing_weakening_strengthened (Γ Δ Ψ : Env) (t : Trm) (T : Typ) :
    typing (Ψ ++ Γ) t T
    → Env.valid_ctx (Ψ ++ Δ ++ Γ)
    → typing (Ψ ++ Δ ++ Γ) t T := by
  intro H p
  apply (typing_weakening_strengthened' _ _ (Ψ ++ Γ))
  exact H
  exact rfl
  exact p

lemma typing_weakening (Γ Δ : Env) (t : Trm) (T : Typ) :
    typing (Γ) t T → Env.valid_ctx (Δ ++ Γ)
    → typing (Δ ++ Γ) t T := by
  intro H p
  rw [← List.nil_append (Δ ++ Γ)] at p
  apply (typing_weakening_strengthened Γ Δ [])
  simp
  exact H
  exact p

lemma typing_weakening_head (Γ : Env) (t : Trm) (T S : Typ) (x : Var):
    ¬ (Env.in_context x Γ) → typing Γ t T
    → typing ((x, S ) :: Γ) t T := by
  intro notxl typt
  rw [← List.nil_append ((x, S ) :: Γ), List.append_cons, List.nil_append]
  apply typing_weakening _ _ _ _ typt
  apply valid_push
  apply (typing_valid_ctx _ _ _ typt)
  exact notxl

--Substitution Rule
lemma typing_subst_var_case (Γ Δ : Env) (u : Trm) (S T : Typ) (z x : Var) :
    Env.binds x T (Δ ++ (z, S ) :: Γ)
    → Env.valid_ctx (Δ ++ (z, S ) :: Γ)
    → typing Γ u S → typing (Δ ++ Γ) ([z // u] ($ x)) T := by
  intro b v t
  simp only [Trm.subst]
  by_cases hxz : x = z
  . simp [if_pos hxz]
    rw [← hxz] at b v
    have h : T = S := by
      apply (binds_mid_eq x T S Γ Δ)
      simp only [← List.append_cons]
      exact b
      simp only [← List.append_cons]
      exact v
    apply typing_weakening
    simp [h, t]
    apply (valid_remove_mid_cons x S Γ Δ v)
  . simp [if_neg hxz]
    apply typing.typ_var
    apply (valid_remove_mid_cons z S Γ Δ v)
    apply binds_remove_mid_cons
    apply b
    push Not at hxz
    exact hxz

lemma typing_regular (t : Trm) (T : Typ) (Γ : Env) :
    typing Γ t T -> Trm.lc t := by
  intro H
  induction H
  case typ_var _ x _ _ _ =>
    exact (Trm.lc.lc_var x)
  case typ_abs L _ u T1 _ _ h' =>
    apply (Trm.lc.lc_abs u T1 L)
    intro x hx
    exact (h' x hx)
  case typ_app _ t1 t2 _ _ _ _ f1 f2 =>
    apply (Trm.lc.lc_app)
    exact f1
    exact f2

lemma typing_subst_strengthened' Γ Δ' t u S T z :
    typing Δ' t T → ((φ : Env) → Δ' = (φ ++ (z, S ) :: Γ)
    → typing (φ ++ (z, S ) :: Γ) t T
    → typing Γ u S → typing (φ ++ Γ) ([z // u] t) T ) := by
  intro H
  induction H
  case typ_var ψ x X h h' =>
    intro φ p G f
    apply typing_subst_var_case
    rw [p] at h'
    exact h'
    rw [p] at h
    exact h
    exact f
  case typ_abs L ψ s S1 S2 h h' =>
    intro Δ p _ f
    simp only [Trm.subst]
    apply typing.typ_abs (L ∪ Env.terms (Δ ++ Γ) ∪ {z}) (Δ ++ Γ) ([z // u] s) S1 S2
    intro x hx
    have hxz : x ≠ z := by
      intro q
      apply hx
      simp [q]
    have hxL : x ∉ L := by
      intro q
      apply hx
      simp [q]
    rw [Trm.subst_open_var s u (typing_regular _ _ _ f) z x (fun q => hxz q.symm)]
    rw [← List.nil_append ((x, S1 ) :: (Δ ++ Γ)), List.append_cons, List.nil_append, ← List.append_assoc]
    apply (h' x hxL)
    simp [p]
    rw [List.append_assoc, ← p]
    simp [h x hxL]
    exact f
  case typ_app ψ t1 t2 S1 S2 h h' f1 f2 =>
    intro φ p _ f
    simp only [Trm.subst]
    apply typing.typ_app
    apply (f1 φ p)
    simp [← p, h]
    exact f
    apply (f2 φ p)
    simp [← p, h']
    exact f

lemma typing_subst_strengthened (Γ Δ : Env) (t u : Trm) (S T : Typ) (z : Var) :
    typing (Δ ++ (z, S ) :: Γ) t T →
    typing Γ u S →
    typing (Δ ++ Γ) ([z // u] t) T := by
  intro H p
  apply (typing_subst_strengthened')
  exact H
  rfl
  exact H
  exact p

lemma typing_subst (Γ : Env) (t u : Trm) (S T : Typ) (z : Var) :
    typing ((z, S ) :: Γ) t T →
    typing Γ u S →
    typing Γ ([z // u] t) T := by
  intro H p
  rw [← List.nil_append ((z, S ) :: Γ)] at H
  rw [← List.nil_append Γ]
  apply typing_subst_strengthened
  exact H
  exact p
--------------------------------------------

lemma typing_rename (Γ : Env) (x y : Var) (t : Trm) (T1 T2 : Typ) :
    x ∉ Trm.fv t →  ¬ (Env.in_context x Γ)
    → y ∉ Trm.fv t →  ¬ (Env.in_context y Γ)
    → typing ((x, T1) :: Γ) (Trm.open₀ t ($ x)) T2
    → typing ((y, T1) :: Γ) (Trm.open₀ t ($ y)) T2 := by
  intro hx fx _ fy R
  by_cases hxy : x = y
  . rwa [hxy] at R
  . have ok_ctx : Env.valid_ctx Γ := by
      apply valid_remove_cons
      apply typing_valid_ctx
      exact R
    have p := Trm.subst_intro t ($ y) (Trm.lc.lc_var y) x hx
    rw [p]
    apply typing_subst ((y, T1) :: Γ) (Trm.open₀ t ($ x)) ($ y) T1 T2
    have q : ((x, T1 ) :: (y, T1 ) :: Γ) = ((([(x, T1)] : Env) ++ (([(y, T1)] : Env))) ++ Γ) := by
      simp
    rw [q]
    apply (typing_weakening_strengthened Γ (([(y, T1)] : Env)) (([(x, T1)] : Env)))
    simp [R]
    apply (valid_push _ _ _ (valid_push _ _ _ ok_ctx fy))
    simp
    push Not
    exact ⟨hxy, fx⟩
    apply typing.typ_var
    apply valid_push _ _ _ ok_ctx fy
    simp

lemma typing_abs_intro (Γ : Env) (x : Var) (t : Trm) (T1 T2 : Typ) :
    x ∉ Trm.fv t →  ¬ (Env.in_context x Γ)
    → typing ((x, T1) :: Γ) (Trm.open₀ t ($ x)) T2
    → typing Γ (Trm.abs T1 t) (T1 -> T2) := by
  intro hx fx R
  apply typing.typ_abs (Trm.fv t ∪ Env.terms Γ)
  intro y hy
  simp at hy
  apply (typing_rename _ _ _ _ _ _ hx fx)
  exact hy.1
  exact (fun q => hy.2 ((context_terms_iff_in_list _ _).mpr q))
  exact R

lemma preservation_beta_red E t T :
    typing E t T
    → ((t' : Trm) →  beta_red t t' → typing E t' T) := by
  intro H
  induction H
  case typ_var φ x S _ _ =>
    intro e' p
    cases p
  case typ_abs L φ t S1 S2 _ a_ih =>
    intro e' p
    cases p
    next t1' L' a' =>
      apply typing.typ_abs (L' ∪ L)
      intro x hx
      simp at hx
      apply (a_ih x hx.2 (Trm.open₀ t1' ($ x)))
      apply (a' x hx.1)
  case typ_app φ t1 t2 S1 S2 f1 f2 h1 h2 =>
    intro e' p
    cases p
    next e1 T lce1 g =>
      cases f1
      next L h =>
        let ⟨x, hx⟩ := Trm.pick_fresh e1 L
        have q : Trm.lc t2 := by
          apply (typing_regular _ _ _ f2)
        simp at hx
        rw [Trm.subst_intro e1 t2 q x hx.2]
        apply (typing_subst)
        exact (h x hx.1)
        exact f2
    next e1 eve1 lct2 =>
      apply typing.typ_app
      apply (h1 e1 eve1)
      exact f2
    next e2 lct1 eve2 =>
      apply typing.typ_app
      exact f1
      apply (h2 e2 eve2)

lemma preservation_multi_red E t T :
    typing E t T
    → ((t' : Trm) →  multi_red t t' → typing E t' T) := by
  intro H t' tmt'
  induction tmt'
  next _ =>
    exact H
  next t2 t3 _ t2bt3 ih =>
      apply (preservation_beta_red _ _ _ ih _ t2bt3)



lemma value_regular (t : Trm) : value t → Trm.lc t := by
  intro valt
  induction valt
  case value_abs _ lcu =>
    exact lcu

--call by value

lemma eval_regular (e1 e2 : Trm) : eval e1 e2 → Trm.lc e1 ∧ Trm.lc e2  := by
  intro ev12
  induction ev12
  case eval_beta u1 u2 lc1 v2 =>
    constructor
    . apply Trm.lc.lc_app
      exact lc1
      exact (value_regular _ v2)
    . apply Trm.open_lc
      exact lc1
      exact (value_regular _ v2)
  case eval_app1 u1 u1' u2 lc2 _ f =>
    constructor
    . apply Trm.lc.lc_app
      exact f.1
      exact lc2
    . apply Trm.lc.lc_app
      exact f.2
      exact lc2
  case eval_app2 u1 u2 u2' lc1 _ f =>
    constructor
    . apply Trm.lc.lc_app
      exact lc1
      exact f.1
    . apply Trm.lc.lc_app
      exact lc1
      exact f.2

lemma preservation_result : Preservation := by
  intro E e e' T H
  revert e'
  induction H
  case typ_var φ x S _ _ =>
    intro e' p
    cases p
  case typ_abs _ φ t S1 S2 _ _ =>
    intro e' p
    cases p
  case typ_app φ t1 t2 S1 S2 f1 f2 h1 h2 =>
    intro e' p
    cases p
    next e1 T lce1 g =>
      cases f1
      next L h =>
        let ⟨x, hx⟩ := Trm.pick_fresh e1 L
        have q : Trm.lc t2 := by
          apply (typing_regular _ _ _ f2)
        simp at hx
        rw [Trm.subst_intro e1 t2 q x hx.2]
        apply (typing_subst)
        exact (h x hx.1)
        exact f2
    next e1 eve1 lct2 =>
      apply typing.typ_app
      apply (h1 e1 eve1)
      exact f2
    next e2 lct1 eve2 =>
      apply typing.typ_app
      exact f1
      apply (h2 e2 eve2)

lemma progress_result : Progress := by
  intro e T H
  generalize p : [] = Γ at H
  induction H
  case typ_var Γ x S _ bx =>
    simp [p.symm] at bx
  case typ_abs L Δ s S1 S2 f _ =>
    left
    apply value.value_abs
    apply Trm.lc.lc_abs s S1 L
    intro x hx
    exact (typing_regular _ _ _ (f x hx))
  case typ_app Δ s1 s2 S1 S2 f g h1 h2 =>
    right
    simp [p] at h1
    simp [p] at h2
    by_cases val1 : value s1
    . by_cases val2 : value s2
      . cases val1
        next s3 T lcs3 =>
          use (Trm.open₀ s3 s2)
          apply eval.eval_beta
          exact lcs3
          exact val2
      . simp [val2] at h2
        rcases h2 with ⟨s3 , hs3⟩
        use (s1 @ s3)
        apply eval.eval_app2
        exact (value_regular _ val1)
        exact hs3
    . simp [val1] at h1
      rcases h1 with ⟨s3 , hs3⟩
      use (s3 @ s2)
      apply eval.eval_app1
      exact (typing_regular _ _ _ g)
      exact hs3



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
      let ⟨x, qx⟩ := Trm.pick_fresh u2' (L ∪ L' ∪ (Trm.fv u1') ∪ (Trm.fv s1') ∪ (Trm.fv s2'))
      simp at qx
      rw [Trm.subst_intro u1' u2' (para_regular _ _ s2pu2').2 x qx.2.2.1]
      rw [Trm.subst_intro s1' s2' (para_regular _ _ s2ps2').2 x qx.2.2.2.1]
      have fact1: ∃ t', para s2' t' ∧ para u2' t' := by
        apply ih2 _ s2pu2'
      have fact2 : ∃ t', para (Trm.open₀ s1' ($ x)) t' ∧ para (Trm.open₀ u1' ($ x)) t' := by
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
        let ⟨x, qx⟩ := Trm.pick_fresh s1' (L ∪ L' ∪ (Trm.fv s1''))
        simp at qx
        have fact1: ∃ t', para s2' t' ∧ para u2' t' := by
          apply ih2 _ s2pu2'
        have fact2 : ∃ t', para (Trm.open₀ s1' ($ x)) t' ∧ para (Trm.open₀ s1'' ($ x)) t' := by
          apply ih1 _ qx.1 _ (f' _ qx.2.1)
        rcases fact1 with ⟨t', qt'⟩
        rcases fact2 with ⟨t'', qt''⟩
        use (Trm.open₀ (Trm.close₀ t'' x) t')
        constructor
        . apply para_through _ _ _ _ x ⟨qx.2.2.2, by simp [Trm.close₀, (Trm.close_var_fv t'' x 0)]⟩
          rw [Trm.open_close_var _ _ (para_regular _ _ qt''.1).2]
          exact qt''.1
          exact qt'.1
        . apply para.para_red _ _ _ _ _ (Trm.fv (Trm.open₀ s1'' ($ x)) ∪ Trm.fv t'' ∪ {x})
          intro y qy
          rw [← Trm.close_open_var x s1'' qx.2.2.1]
          apply open_close_para _ _ _ _ qt''.2 qy
          exact qt'.2
  case para_app s1 s1' s2 s2' s1ps1' _ ih1 ih2 =>
      intro t2 tpt2
      cases tpt2
      case para_red t1' u1' u2' T L f s2pu2' =>
        cases s1ps1'
        next s1'' L' f' =>
          let ⟨x, qx⟩ := Trm.pick_fresh u1' (L ∪ L' ∪ (Trm.fv s1''))
          simp at qx
          have fact1: ∃ t', para s2' t' ∧ para u2' t' := by
            apply ih2 _ s2pu2'
          have fact2 : ∃ t', para (λT, s1'') t' ∧ para (λT, u1') t' := by
            apply ih1 (λT, u1') (para.para_abs _ _ _ L f)
          rcases fact1 with ⟨t', qt'⟩
          rcases fact2 with ⟨t'', qt''⟩
          cases qt''.1
          next w1 L'' f'' =>
            cases qt''.2
            next L''' f''' =>
              use (Trm.open₀ w1 t')
              constructor
              . apply para.para_red _ _ _ _ _ L'' f'' qt'.1
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
        . apply para.para_app _ _ _ _ qt'.1 qt''.1
        . apply para.para_app _ _ _ _ qt'.2 qt''.2
  case para_abs s1 s2' T L _ ih =>
    intro t2 tpt2
    cases tpt2
    next t2' L' f' =>
      let ⟨x, qx⟩ := Trm.pick_fresh s2' (L ∪ L' ∪ (Trm.fv t2'))
      simp at qx
      have fact1 := ih x qx.1 _ (f' x qx.2.1)
      rcases fact1 with ⟨t', qt'⟩
      use (λT, (Trm.close₀ t' x))
      constructor
      . apply para.para_abs _ _ _ (Trm.fv (Trm.open₀ s2' ($ x)) ∪ Trm.fv t' ∪ {x})
        intro y qy
        rw [← Trm.close_open_var x s2' qx.2.2.2]
        apply open_close_para _ _ _ _ qt'.1 qy
      . apply para.para_abs _ _ _ (Trm.fv (Trm.open₀ t2' ($ x)) ∪ Trm.fv t' ∪ {x})
        intro y qy
        rw [← Trm.close_open_var x t2' qx.2.2.1]
        apply open_close_para _ _ _ _ qt'.2 qy

lemma multi_para_diamond_core t t1 t2 :
    (para t t1) ∧ (multi_para t t2)
    → ∃ t', (multi_para t1 t') ∧ (para t2 t') := by
  intro ⟨tpt1, tmt2⟩
  induction tmt2
  case m_para_refl _ =>
    use t1
    constructor
    apply multi_para.m_para_refl
    exact (para_regular _ _ tpt1).2
    exact tpt1
  case m_para_head s1 s2 _ s1ps2 h =>
    rcases h with ⟨t' , ⟨h1, h2⟩⟩
    have q := (para_diamond _ _ s1ps2 _ h2)
    rcases q with ⟨t'', ⟨h3, h4⟩⟩
    use t''
    constructor
    exact (multi_para.m_para_head _ _ _ h1 h4)
    exact h3

lemma multi_para_diamond t t1 t2 :
    (multi_para t t1) ∧ (multi_para t t2)
    → ∃ t', (multi_para t1 t') ∧ (multi_para t2 t') := by
  intro ⟨tmpt1 , tmpt2⟩
  induction tmpt1
  case m_para_refl _ =>
    use t2
    exact ⟨tmpt2, multi_para.m_para_refl t2 (multi_para_regular _ _ tmpt2).2⟩
  case m_para_head s1 s2 _ s1ps2 f =>
    rcases f with ⟨t', ⟨h1,h2⟩⟩
    have q := (multi_para_diamond_core _ _ _ ⟨s1ps2, h1⟩)
    rcases q with ⟨t'', ⟨h3, h4⟩⟩
    use t''
    constructor
    exact h3
    exact (multi_para.m_para_head _ _ _ h2 h4)

theorem beta_red_confluence :
    ∀ t t1 t2, (multi_red t t1) ∧ (multi_red t t2)
    → ∃ t', (multi_red t1 t') ∧ (multi_red t2 t') := by
  intro t t1 t2 ⟨trt1 , trt2⟩
  simp [multi_red_iff_multi_para] at trt1 trt2 ⊢
  exact (multi_para_diamond t t1 t2 ⟨trt1 , trt2⟩)



namespace Trm

-- Defining substitutions over contexts --
@[simp]
def multi_subst (L : Finset Var) (f : L → Trm) : Trm → Trm
| bvar i => bvar i
| fvar y => if h : (y ∈ L) then (f ⟨y, h⟩) else (fvar y)
| abs T u => abs T (multi_subst L f u)
| app u1 u2 => app (multi_subst L f u1) (multi_subst L f u2)

--context_type takes a term in a Env and outputs its type
@[simp]
def context_type Γ (x : Env.terms Γ) : Typ :=
  match Γ, x with
  | [], ⟨_, h⟩ => by simp [Env.terms] at h
  | (x, T) :: Γ, ⟨x', h⟩ =>
    if ha : x' = x then
      T
    else
      context_type Γ ⟨x', by simpa [Env.terms, ha] using h⟩

--substitution over the empty Env does nothing
lemma multi_subst_over_emp t (f : Env.terms [] → Trm) :
    (multi_subst (Env.terms []) f t) = t := by
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
    (f : Env.terms (([(x, T)] : Env)) → Trm)
    → (multi_subst (Env.terms (([(x, T)] : Env))) f t)
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

--if we have a function of terms of a Env, say f,
--for a term u and variable x, we can extend the f with mapping x → u
@[simp]
def add_term Γ (f : Env.terms Γ → Trm)
    (u : Trm) y T (x : Env.terms ((y, T) :: Γ)) : Trm := by
  rcases x with ⟨x' , h⟩
  by_cases p : x' = y
  . exact u
  . simp [p] at h
    exact f ⟨x' , h⟩

--If y does not appear in t, then substitution over a Env (y,T) ++ Γ
--is the same as substitution over Γ
lemma multi_subst_fresh Γ t u y T (h : y ∉ (fv t)) (f : Env.terms Γ → Trm) :
    (multi_subst (Env.terms ((y, T) :: Γ)) (add_term Γ f u y T) t)
     = (multi_subst (Env.terms Γ) f t) := by
  induction t
  case bvar i =>
    rfl
  case fvar x =>
    simp [fv] at h
    simp only [multi_subst, Env.terms, Finset.mem_union, Finset.mem_singleton, add_term]
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


--substitution over a Env distributes over opening
lemma multi_subst_open_lemma_1 t1 t2 Γ : (f : Env.terms Γ → Trm)
   → (∀ x (h : x ∈ Env.terms Γ), lc (f ⟨x,h⟩)) → (j : ℕ)
   → (multi_subst (Env.terms Γ) f ({j ~> t2} t1))
     = ({j ~> multi_subst (Env.terms Γ) f t2} (multi_subst (Env.terms Γ) f t1)) := by
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
   by_cases hy : (y ∈ Env.terms Γ)
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
    → (f : Env.terms Γ → Trm)
    → (∀ x (h : x ∈ Env.terms Γ), lc (f ⟨x,h⟩))
    → (multi_subst (Env.terms ((y, T) :: Γ)) (add_term Γ f u y T) (open₀ t ($ y)))
      = (open₀ (multi_subst (Env.terms Γ) f t) u) := by
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
lemma multi_subst_open Γ t y : y ∉ Env.terms Γ
    → (f : Env.terms Γ → Trm)
    → (∀ x (h : x ∈ Env.terms Γ), lc (f ⟨x,h⟩))
    → (multi_subst (Env.terms Γ) f (open₀ t ($ y)))
      = (open₀ (multi_subst (Env.terms Γ) f t) ($ y)) := by
  intro hy f lcf
  rw [open₀ , multi_subst_open_lemma_1, multi_subst, ← open₀]
  simp [hy]
  apply lcf

--if (x,T) appears in Env Γ, then the Env map sends Γ x to T
lemma context_type_eq_bind Γ (x : Env.terms Γ) T :
    Env.valid_ctx Γ → Env.binds x T Γ → context_type Γ x = T := by
  induction Γ
  case nil =>
    intro _ bnd
    cases bnd
  case cons h Γ' ih =>
    rcases h with ⟨y, S⟩
    intro vld bnd
    simp only [context_type, Env.terms]
    by_cases p : y = ↑x
    . simp [p] at bnd ⊢
      apply bnd
    . have q : (↑x ≠ y) := (fun z => p (z.symm))
      simp [q]
      apply ih
      apply valid_remove_cons _ _ _ vld
      apply binds_remove_mid_cons ↑x y T S Γ' [] bnd
      symm
      exact p

--if a term is locally closed, and there is list of locally closed terms, then
--substition with these terms is also locally closed.
lemma multi_subst_lc t Γ : lc t
    → (f : Env.terms Γ → Trm)
    → (∀ x (h : x ∈ Env.terms Γ), lc (f ⟨x,h⟩))
    → lc ((multi_subst (Env.terms Γ) f t)) := by
  intro lct f lcf
  induction lct
  case lc_var y =>
    rw [multi_subst]
    by_cases hxy : y ∈ Env.terms Γ
    . simp [if_pos, hxy]
      exact (lcf y hxy)
    . simp [if_neg, hxy]
      exact (lc.lc_var y)
  case lc_abs u T L a hu =>
    simp
    apply lc.lc_abs _ _ (L ∪ (Env.terms Γ))
    intro x hx
    simp at hx
    rw [← multi_subst_open Γ u x hx.2 f lcf]
    apply hu x hx.1
  case lc_app u1 u2 lcu1 lcu2 hu1 hu2 =>
    dsimp [multi_subst]
    apply (lc.lc_app _ _ hu1 hu2)

end Trm


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
      push Not at F
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
  | Typ.typ_all => {t | (lc t) ∧ SN t}
  | Typ.typ_arrow t1 t2 =>
    {t | (lc t) ∧ (∀ u, ((lc u) ∧ (u ∈ SC t1)) → (t @ u) ∈ SC t2)}

-- By definition, strongly computable terms are locally closed.
lemma SC_regular A t : t ∈ (SC A) → lc t := by
  intro H
  induction A
  case typ_all =>
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
  case typ_all =>
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
  case typ_all =>
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
        apply (ih1 ($ x)).2 (lc.lc_var x) (by simp)
        intro t' nbt
        cases nbt
      have this3 : (app t ($ x)) ∈ SC A2 := H ($ x) ⟨lc.lc_var x , this2⟩
      have this4 : SN (app t ($ x)) := (ih2 (app t ($ x))).1 this3
      apply (SN_app1 _ _ (lc.lc_var x) this4)
    . intro lct nt F --CR3 arrow case
      constructor
      . exact lct
      . intro u Hu
        have this1 : SN u := (ih1 _).1 Hu.2
        induction this1
        case sn u _ ihu =>
        apply (ih2 (t @ u)).2 (lc.lc_app _ _ lct Hu.1) (by simp)
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
  case typ_all =>
    constructor
    . apply lc.lc_var x
    . apply SN.sn
      intro t tbx
      cases tbx
  case typ_arrow A1 A2 _ _ =>
    apply CR3 _ _ (lc.lc_var x) (by simp)
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
      rw [subst_intro t ($ y) (lc.lc_var y) y hy]
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
        apply CR3 _ _ (lc.lc_app _ _ lct Hu.1) (by simp)
        intro t'' bred
        cases bred
        next lct' lcu =>
          let ⟨z, hz⟩ := pick_fresh t ∅
          simp at hz
          rw [subst_intro _ _ Hu.1 z hz]
          apply (F u z hz Hu.2)
        next t1' t'bt1' lcu =>
          cases t'bt1'
          next t'' L a =>
            let ⟨x, hx⟩ := pick_fresh t (L ∪ (fv t''))
            simp at hx
            have this3 : beta_red (open₀ t ($ y)) (open₀ t'' ($ y)) := by
              rw [subst_intro t ($ y) (lc.lc_var y) x hx.2.2]
              rw [subst_intro t'' ($ y) (lc.lc_var y) x hx.2.1]
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
    → (f : (Env.terms Γ) → Trm)
    → (∀ x (h : x ∈ (Env.terms Γ)), (f ⟨x, h⟩) ∈ SC (context_type Γ ⟨x, h⟩))
    → (multi_subst (Env.terms Γ) f t) ∈ SC A := by
  intro typt
  induction typt
  case typ_var Δ y T vld bnd =>
    intro f Hf
    simp only [multi_subst]
    by_cases h : y ∈ Env.terms Δ
    . simp [h, ← context_type_eq_bind Δ ⟨y, h⟩ T vld bnd]
      apply (Hf y h)
    . simp [h]
      apply SC_var
  case typ_abs L Δ u T1 T2 a ih =>
    intro f Hf
    apply SC_lambda_term
    rw [← multi_subst]
    apply multi_subst_lc _ _ (typing_regular _ _ _ (typing.typ_abs L Δ u T1 T2 a))
    exact (fun x hx => (SC_regular _ _ (Hf x hx)))
    intros u1 scu1
    let ⟨x, hx⟩ := pick_fresh u L
    simp at hx
    have this : (∀ y (s : y ∈ (Env.terms ((x, T1) :: Δ))),
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
      apply R (multi_subst (Env.terms Δ) f t2)
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
  let f : Env.terms (([(x, T)] : Env)) → Trm := fun _ => ($ x)
  have this : multi_subst (Env.terms (([(x, T)] : Env))) f t = t := by
    rw [multi_subst_at_singleton]
    rw [subst_fresh _ _ _ hx]
  rw [← this]
  apply SC_subst
  apply typing_weakening [] (([(x, T)] : Env)) _ _ typt
  apply valid_push _ _ _ (Env.valid_ctx.valid_nil) (by simp)
  exact (fun y hy => SC_var _ _)

end Trm


theorem typing_unique :
    ∀ t, Trm.lc t → ∀ Γ T1 T2,
    typing Γ t T1 → typing Γ t T2 → T1 = T2 := by
  intro t lct
  induction lct
  case lc_var x =>
    intro Γ T1 T2 ty1 ty2
    cases ty1
    next _ bnd =>
      cases ty2
      next _ bnd' =>
        simp [Env.binds] at bnd bnd'
        rw [bnd] at bnd'
        simp at bnd'
        exact bnd'
  case lc_abs u T L a ih =>
    intro Γ T1 T2 ty1 ty2
    cases ty1
    next L1 U1 h1 =>
      cases ty2
      next L2 U2 h2 =>
        have ⟨x,hx⟩ := Trm.pick_fresh u (L ∪ L1 ∪ L2)
        simp at hx ⊢
        apply ih x hx.1 ((x, T) :: Γ) U1 U2 (h1 x hx.2.1) (h2 x hx.2.2.1)
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
    ∀ t Γ, Trm.lc t → Env.valid_ctx Γ →
    (∃ T, typing Γ t T) ∨ ¬ (∃ T, typing Γ t T) := by
  intro t Γ lct vld
  induction lct generalizing Γ
  case lc_var x =>
    match h : (Env.get x Γ) with
    | some T =>
        left
        use T
        apply typing.typ_var Γ x T vld h
    | none =>
        right
        rintro ⟨T, typ⟩
        cases typ
        next _ ih =>
          simp [h] at ih
  case lc_abs u T L a ih =>
    have ⟨x,hx⟩ := Trm.pick_fresh u (L ∪ Env.terms Γ)
    simp at hx
    cases H : (ih x hx.1 ((x, T) :: Γ)
        (valid_push Γ x T vld (not_context_terms_to_not_in_context _ _ hx.2.1)))
    next pos =>
      rcases pos with ⟨S, p⟩
      left
      use (T -> S)
      apply (typing.typ_abs (Trm.fv u ∪ Env.terms Γ) Γ)
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
        have ⟨z,hz⟩ := Trm.pick_fresh u (L' ∪ Env.terms Γ)
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
        | Typ.typ_all =>
          right
          rintro ⟨T, P⟩
          cases P
          next S ty1 ty2 =>
            have q:= typing_unique _ lc1 _ _ _ p1 ty2
            simp at (q)
        | Typ.typ_arrow S1 S2 =>
          by_cases h : S1 = S
          . left
            use S2
            rw [← h] at p2
            apply typing.typ_app Γ t1 t2 S1 S2 p1 p2
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
    Trm.lc t → Env.valid_ctx Γ → (typing Γ t T) ∨ ¬(typing Γ t T) := by
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
