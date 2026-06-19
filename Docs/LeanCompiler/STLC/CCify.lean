import «LeanCompiler».STLC.CPS
import «LeanCompiler».STLC.CC

namespace LeanCompiler.STLC.CCify

open LeanCompiler.STLC.CPS
open LeanCompiler.STLC.CC

inductive CPrimops (var : CType → Type) (t : PType) : Type where
  | ret : var (.data t) → CPrimops var t
  | let_ : CPrimop var ty → (var ty → CPrimops var t) → CPrimops var t

@[simp] def CPrimops.denote {t : PType} : CPrimops CType.denote t → PType.denote t
  | .ret v => v
  | .let_ p k => CPrimops.denote (k (CPrimop.denote p))

mutual
  @[simp] def splicePrim {var : CType → Type} {t t' : PType} :
      CPrimops var t → (var (.data t) → CPrimops var t') → CPrimops var t'
    | .ret v, k => k v
    | .let_ p k1, k2 => .let_ p (fun x => splicePrim (k1 x) k2)

  @[simp] def spliceTerm {var : CType → Type} {result t : PType} :
      CPrimops var t → (var (.data t) → CTerm var result) → CTerm var result
    | .ret v, k => k v
    | .let_ p k1, k2 => .bind p (fun x => spliceTerm (k1 x) k2)
end

@[simp] def spliceFuncs' {var : CType → Type} {result : PType} {α β : Type} :
    CFuncs var result α → (α → β) → CFuncs var result β
  | .main v, f => .main (f v)
  | .abs e fs, f => .abs e (fun code => spliceFuncs' (fs code) f)

@[simp] def spliceFuncs {var : CType → Type} {result : PType} {α β γ : Type} :
    CFuncs var result α → CFuncs var result β → (α → β → γ) → CFuncs var result γ
  | .main v, fs2, f => spliceFuncs' fs2 (f v)
  | .abs e fs1, fs2, f => .abs e (fun code => spliceFuncs (fs1 code) fs2 f)

@[simp] def inside {var : CType → Type} {result : PType} {α β : Type} :
    CFuncs var result α → (α → CFuncs var result β) → CFuncs var result β
  | .main v, f => f v
  | .abs e fs, f => .abs e (fun code => inside (fs code) f)

structure NatVar (_ : PType) : Type where
  idx : Nat

@[simp] def lookupType : List PType → Nat → Option PType
  | [], _ => none
  | first :: rest, n =>
      if n = rest.length then
        some first
      else
        lookupType rest n

abbrev Ok (envT : List PType) (n : Nat) (t : PType) : Prop :=
  lookupType envT n = some t

mutual
  inductive WfTerm : (envT : List PType) → {result : PType} → PTerm NatVar result → Prop where
    | halt {envT result} {n : NatVar result} :
        Ok envT n.idx result →
        WfTerm envT (.halt n)
    | app {envT result t} {n1 : NatVar (.cont t)} {n2 : NatVar t} :
        Ok envT n1.idx (.cont t) →
        Ok envT n2.idx t →
        WfTerm envT (.app (result := result) (t := t) n1 n2)
    | bind {envT result t} {p : PPrimop NatVar result t} {e : NatVar t → PTerm NatVar result} :
        WfPrimop envT p →
        WfTerm (t :: envT) (e ⟨envT.length⟩) →
        WfTerm envT (.bind p e)

  inductive WfPrimop : (envT : List PType) → {result t : PType} → PPrimop NatVar result t → Prop where
    | var {envT result t} {n : NatVar t} :
        Ok envT n.idx t →
        WfPrimop envT (.var (result := result) (t := t) n)
    | tru {envT result} :
        WfPrimop envT (.tru (result := result))
    | fals {envT result} :
        WfPrimop envT (.fals (result := result))
    | abs {envT result t} {e : NatVar t → PTerm NatVar result} :
        WfTerm (t :: envT) (e ⟨envT.length⟩) →
        WfPrimop envT (.abs e)
    | pair {envT result t1 t2} {n1 : NatVar t1} {n2 : NatVar t2} :
        Ok envT n1.idx t1 →
        Ok envT n2.idx t2 →
        WfPrimop envT (.pair (result := result) (t1 := t1) (t2 := t2) n1 n2)
    | fst {envT result t1 t2} {n : NatVar (.prod t1 t2)} :
        Ok envT n.idx (.prod t1 t2) →
        WfPrimop envT (.fst (result := result) (t1 := t1) (t2 := t2) n)
    | snd {envT result t1 t2} {n : NatVar (.prod t1 t2)} :
        Ok envT n.idx (.prod t1 t2) →
        WfPrimop envT (.snd (result := result) (t1 := t1) (t2 := t2) n)
end

@[simp] def envType : List PType → PType
  | [] => .unit
  | t :: envT => .prod t (envType envT)

@[simp] def envOf (var : CType → Type) : List PType → Type
  | [] => PUnit
  | t :: envT => var (.data t) × envOf var envT

@[simp] def lookup {var : CType → Type} :
    (envT : List PType) → (n : Nat) → envOf var envT →
      {t : PType} → Ok envT n t → var (.data t)
  | [], _, _, _, h => by cases h
  | first :: rest, n, env, t, h =>
      if hn : n = rest.length then
        have hSome : some first = some t := by
          have hLookup : lookupType (first :: rest) n = some t := h
          have hLookup' :
              (if n = rest.length then some first else lookupType rest n) = some t := by
            simpa [lookupType] using hLookup
          simpa [hn] using hLookup'
        match Option.some.inj hSome with
        | rfl => env.1
      else
        have hRest : lookupType rest n = some t := by
          have hLookup : lookupType (first :: rest) n = some t := h
          simpa [lookupType, hn] using hLookup
        lookup rest n env.2 (t := t) hRest

@[simp] def packTerm {var : CType → Type} :
    (envT : List PType) → envOf var envT → CPrimops var (envType envT)
  | [], _ => .let_ .unitIntro (fun u => .ret u)
  | _t :: envT, (x, env) =>
      splicePrim (packTerm envT env) (fun envx =>
        .let_ (.pair x envx) (fun p => .ret p))

@[simp] def unpackVar {var : CType → Type} {result : PType} :
    (envT : List PType) → var (.data (envType envT)) →
      (envOf var envT → CTerm var result) → CTerm var result
  | [], _envx, k => k PUnit.unit
  | _t :: envT, envx, k =>
      .bind (.fst envx) (fun x =>
        .bind (.snd envx) (fun envx' =>
          unpackVar envT envx' (fun env => k (x, env))))

@[simp] def unpackTerm {var : CType → Type} {result : PType} :
    (envT : List PType) → CPrimops var (envType envT) →
      (envOf var envT → CTerm var result) → CTerm var result
  | envT, ps, k =>
      spliceTerm ps (fun envx => unpackVar envT envx k)

abbrev EnvProg (var : CType → Type) (result : PType) (envT : List PType) : Type :=
  CFuncs var result (envOf var envT → CTerm var result)

abbrev EnvPrimops (var : CType → Type) (result : PType) (envT : List PType) (t : PType) : Type :=
  CFuncs var result (envOf var envT → CPrimops var t)

@[simp] theorem wfTerm_halt_inv {envT : List PType} {result : PType} {n : NatVar result} :
    WfTerm envT (.halt n) → Ok envT n.idx result := by
  intro hWf
  cases hWf with
  | halt h => exact h

@[simp] theorem wfTerm_app_inv {envT : List PType} {result t : PType}
    {n1 : NatVar (.cont t)} {n2 : NatVar t} :
    WfTerm envT (.app (result := result) (t := t) n1 n2) →
      Ok envT n1.idx (.cont t) ∧ Ok envT n2.idx t := by
  intro hWf
  cases hWf with
  | app h1 h2 => exact ⟨h1, h2⟩

@[simp] theorem wfTerm_bind_inv {envT : List PType} {result t : PType}
    {p : PPrimop NatVar result t} {e : NatVar t → PTerm NatVar result} :
    WfTerm envT (.bind p e) →
      WfPrimop envT p ∧ WfTerm (t :: envT) (e ⟨envT.length⟩) := by
  intro hWf
  cases hWf with
  | bind h1 h2 => exact ⟨h1, h2⟩

@[simp] theorem wfPrimop_var_inv {envT : List PType} {result t : PType} {n : NatVar t} :
    WfPrimop envT (.var (result := result) (t := t) n) →
      Ok envT n.idx t := by
  intro hWf
  cases hWf with
  | var h => exact h

@[simp] theorem wfPrimop_abs_inv {envT : List PType} {result t : PType}
    {e : NatVar t → PTerm NatVar result} :
    WfPrimop envT (.abs e) →
      WfTerm (t :: envT) (e ⟨envT.length⟩) := by
  intro hWf
  cases hWf with
  | abs h => exact h

@[simp] theorem wfPrimop_pair_inv {envT : List PType} {result t1 t2 : PType}
    {n1 : NatVar t1} {n2 : NatVar t2} :
    WfPrimop envT (.pair (result := result) (t1 := t1) (t2 := t2) n1 n2) →
      Ok envT n1.idx t1 ∧ Ok envT n2.idx t2 := by
  intro hWf
  cases hWf with
  | pair h1 h2 => exact ⟨h1, h2⟩

@[simp] theorem wfPrimop_fst_inv {envT : List PType} {result t1 t2 : PType}
    {n : NatVar (.prod t1 t2)} :
    WfPrimop envT (.fst (result := result) (t1 := t1) (t2 := t2) n) →
      Ok envT n.idx (.prod t1 t2) := by
  intro hWf
  cases hWf with
  | fst h => exact h

@[simp] theorem wfPrimop_snd_inv {envT : List PType} {result t1 t2 : PType}
    {n : NatVar (.prod t1 t2)} :
    WfPrimop envT (.snd (result := result) (t1 := t1) (t2 := t2) n) →
      Ok envT n.idx (.prod t1 t2) := by
  intro hWf
  cases hWf with
  | snd h => exact h

mutual
  def ccTerm (var : CType → Type) (result : PType)
      (e : PTerm NatVar result) (envT : List PType) :
      WfTerm envT e → EnvProg var result envT :=
    match e with
    | .halt n =>
        fun hWf =>
          .main (fun env =>
            .halt (lookup envT n.idx env (t := result) (wfTerm_halt_inv hWf)))
    | .app (t := t) n1 n2 =>
        fun hWf =>
          .main (fun env =>
            .app
              (lookup envT n1.idx env (t := .cont t) (wfTerm_app_inv hWf).1)
              (lookup envT n2.idx env (t := t) (wfTerm_app_inv hWf).2))
    | .bind (t := t) p e' =>
        fun hWf =>
          let hBind := wfTerm_bind_inv hWf
          spliceFuncs
            (ccPrimop var result t p envT hBind.1)
            (ccTerm var result (e' ⟨envT.length⟩) (t :: envT) hBind.2)
            (fun p' e'' env =>
              spliceTerm (p' env) (fun x => e'' (x, env)))

  def ccPrimop (var : CType → Type) (result t : PType)
      (p : PPrimop NatVar result t) (envT : List PType) :
      WfPrimop envT p → EnvPrimops var result envT t :=
    match p with
    | .var (t := t) n =>
        fun hWf =>
          .main (fun env =>
            .let_ (.var (lookup envT n.idx env (t := t) (wfPrimop_var_inv hWf))) (fun x => .ret x))
    | .tru =>
        fun _hWf =>
          .main (fun _ =>
            .let_ .tru (fun x => .ret x))
    | .fals =>
        fun _hWf =>
          .main (fun _ =>
            .let_ .fals (fun x => .ret x))
    | .abs (t := t) body =>
        fun hWf =>
          inside (ccTerm var result (body ⟨envT.length⟩) (t :: envT) (wfPrimop_abs_inv hWf))
            (fun body' =>
              .abs (env := envType envT)
                (fun envx arg =>
                  unpackTerm envT (.ret envx) (fun env => body' (arg, env)))
                (fun code =>
                  .main (fun env =>
                    splicePrim (packTerm envT env) (fun envx =>
                      .let_ (.pack code envx) (fun closure => .ret closure)))))
    | .pair (t1 := t1) (t2 := t2) n1 n2 =>
        fun hWf =>
          .main (fun env =>
            .let_ (.pair
              (lookup envT n1.idx env (t := t1) (wfPrimop_pair_inv hWf).1)
              (lookup envT n2.idx env (t := t2) (wfPrimop_pair_inv hWf).2))
              (fun x => .ret x))
    | .fst (t1 := t1) (t2 := t2) n =>
        fun hWf =>
          .main (fun env =>
            .let_ (.fst (lookup envT n.idx env (t := .prod t1 t2) (wfPrimop_fst_inv hWf)))
              (fun x => .ret x))
    | .snd (t1 := t1) (t2 := t2) n =>
        fun hWf =>
          .main (fun env =>
            .let_ (.snd (lookup envT n.idx env (t := .prod t1 t2) (wfPrimop_snd_inv hWf)))
              (fun x => .ret x))
end

@[simp] def mapFuncs {var : CType → Type} {result : PType} {α β : Type}
    (f : α → β) : CFuncs var result α → CFuncs var result β
  | .main v => .main (f v)
  | .abs e fs => .abs e (fun x => mapFuncs f (fs x))

theorem mapFuncs_correct {result : PType} {α β : Type}
    (f : α → β)
    (fs : CFuncs CType.denote result α)
    (k : PType.denote result → Bool) :
    CFuncs.denote (mapFuncs f fs) k = f (CFuncs.denote fs k) := by
  induction fs with
  | main v =>
      rfl
  | abs e fs ih =>
      simp [mapFuncs, CFuncs.denote, ih]

theorem splicePrim_correct {t t' : PType}
    (ps : CPrimops CType.denote t)
    (ps' : CType.denote (.data t) → CPrimops CType.denote t') :
    CPrimops.denote (splicePrim ps ps') =
      CPrimops.denote (ps' (CPrimops.denote ps)) := by
  induction ps with
  | ret v =>
      rfl
  | let_ p k ih =>
      simp [splicePrim, CPrimops.denote, ih]

theorem spliceTerm_correct {result t : PType}
    (ps : CPrimops CType.denote t)
    (e : CType.denote (.data t) → CTerm CType.denote result)
    (k : PType.denote result → Bool) :
    CTerm.denote (spliceTerm ps e) k =
      CTerm.denote (e (CPrimops.denote ps)) k := by
  induction ps with
  | ret v =>
      rfl
  | let_ p k' ih =>
      simp [spliceTerm, CTerm.denote, CPrimops.denote, ih]

theorem spliceFuncs'_correct {result : PType} {α β : Type}
    (fs : CFuncs CType.denote result α)
    (f : α → β)
    (k : PType.denote result → Bool) :
    CFuncs.denote (spliceFuncs' fs f) k = f (CFuncs.denote fs k) := by
  induction fs with
  | main v =>
      rfl
  | abs e fs ih =>
      simp [spliceFuncs', CFuncs.denote, ih]

theorem spliceFuncs_correct {result : PType} {α β γ : Type}
    (fs1 : CFuncs CType.denote result α)
    (fs2 : CFuncs CType.denote result β)
    (f : α → β → γ)
    (k : PType.denote result → Bool) :
    CFuncs.denote (spliceFuncs fs1 fs2 f) k =
      f (CFuncs.denote fs1 k) (CFuncs.denote fs2 k) := by
  induction fs1 with
  | main v =>
      simpa [spliceFuncs] using spliceFuncs'_correct fs2 (f v) k
  | abs e fs ih =>
      simp [spliceFuncs, CFuncs.denote, ih]

theorem inside_correct {result : PType} {α β : Type}
    (fs1 : CFuncs CType.denote result α)
    (fs2 : α → CFuncs CType.denote result β)
    (k : PType.denote result → Bool) :
    CFuncs.denote (inside fs1 fs2) k =
      CFuncs.denote (fs2 (CFuncs.denote fs1 k)) k := by
  induction fs1 with
  | main v =>
      rfl
  | abs e fs ih =>
      simp [inside, CFuncs.denote, ih]

@[simp] def envPackVal : (envT : List PType) → envOf CType.denote envT → PType.denote (envType envT)
  | [], _ => PUnit.unit
  | _t :: envT, (x, env) => (x, envPackVal envT env)

@[simp] def envUnpackVal : (envT : List PType) → PType.denote (envType envT) → envOf CType.denote envT
  | [], _ => PUnit.unit
  | _t :: envT, p => (p.1, envUnpackVal envT p.2)

@[simp] theorem envPackUnpack {envT : List PType} (v : PType.denote (envType envT)) :
    envPackVal envT (envUnpackVal envT v) = v := by
  induction envT with
  | nil =>
      cases v
      rfl
  | cons t envT ih =>
      cases v with
      | mk v1 v2 =>
          simp [envPackVal, envUnpackVal, ih]

@[simp] theorem envUnpackPack {envT : List PType} (env : envOf CType.denote envT) :
    envUnpackVal envT (envPackVal envT env) = env := by
  induction envT with
  | nil =>
      cases env
      rfl
  | cons t envT ih =>
      cases env with
      | mk x rest =>
          simp [envPackVal, envUnpackVal, ih]

theorem packTerm_correct (envT : List PType) (env : envOf CType.denote envT) :
    CPrimops.denote (packTerm envT env) = envPackVal envT env := by
  induction envT with
  | nil =>
      simp [packTerm, envPackVal]
  | cons t envT ih =>
      cases env with
      | mk x rest =>
          simp [packTerm, envPackVal, splicePrim_correct, ih]

theorem unpackVar_correct {result : PType}
    (envT : List PType)
    (envx : CType.denote (.data (envType envT)))
    (e : envOf CType.denote envT → CTerm CType.denote result)
    (k : PType.denote result → Bool) :
    CTerm.denote (unpackVar envT envx e) k =
      CTerm.denote (e (envUnpackVal envT envx)) k := by
  induction envT with
  | nil =>
      simp [unpackVar, envUnpackVal]
  | cons t envT ih =>
      cases envx with
      | mk x rest =>
          simp [unpackVar, envUnpackVal, ih, CTerm.denote]

theorem unpackTerm_correct {result : PType}
    (envT : List PType)
    (ps : CPrimops CType.denote (envType envT))
    (e : envOf CType.denote envT → CTerm CType.denote result)
    (k : PType.denote result → Bool) :
    CTerm.denote (unpackTerm envT ps e) k =
      CTerm.denote (e (envUnpackVal envT (CPrimops.denote ps))) k := by
  calc
    CTerm.denote (unpackTerm envT ps e) k
        = CTerm.denote (unpackVar envT (CPrimops.denote ps) e) k := by
          simpa [unpackTerm]
            using spliceTerm_correct (ps := ps) (e := fun envx => unpackVar envT envx e) (k := k)
    _ = CTerm.denote (e (envUnpackVal envT (CPrimops.denote ps))) k := by
          simpa using unpackVar_correct (envT := envT) (envx := CPrimops.denote ps) (e := e) (k := k)

abbrev UnitVar (_ : PType) := PUnit

def CtxOk (envT : List PType) (G : Ctxt NatVar UnitVar) : Prop :=
  ∀ {t : PType} {v1 : NatVar t} {v2 : UnitVar t},
    mkPair v1 v2 ∈ G → Ok envT v1.idx t

theorem lookup_proof_irrel
    {envT : List PType} {n : Nat} {t : PType}
    (env : envOf CType.denote envT)
    (h1 h2 : Ok envT n t) :
    lookup envT n env (t := t) h1 = lookup envT n env (t := t) h2 := by
  have hEq : h1 = h2 := Subsingleton.elim h1 h2
  cases hEq
  rfl

theorem lookupType_ge_none :
    ∀ (envT : List PType) (n : Nat), envT.length ≤ n → lookupType envT n = none
  | [], _n, _h => rfl
  | _t :: rest, n, h => by
      by_cases hn : n = rest.length
      · have hContra : False := by
          have : Nat.succ rest.length ≤ rest.length := by simpa [hn] using h
          exact Nat.not_succ_le_self _ this
        exact False.elim hContra
      · have hRest : rest.length ≤ n := Nat.le_trans (Nat.le_succ _) h
        simpa [lookupType, hn] using lookupType_ge_none rest n hRest

@[simp] theorem lookupType_length_none (envT : List PType) :
    lookupType envT envT.length = none :=
  lookupType_ge_none envT envT.length (Nat.le_refl _)

theorem ok_weaken {envT : List PType} {n : Nat} {t t' : PType} :
    Ok envT n t → Ok (t' :: envT) n t := by
  intro hOk
  unfold Ok at *
  by_cases hn : n = envT.length
  · have hNone : lookupType envT n = none := by
      subst hn
      exact lookupType_length_none envT
    have : False := by
      simp [hNone] at hOk
    exact False.elim this
  · simpa [lookupType, hn] using hOk

def CtxVal (envT : List PType) (env : envOf CType.denote envT)
    (G : Ctxt NatVar PType.denote) : Prop :=
  ∀ {t : PType} {v1 : NatVar t} {v2 : PType.denote t},
    mkPair v1 v2 ∈ G →
      ∃ h : Ok envT v1.idx t, lookup envT v1.idx env (t := t) h = v2

theorem ctxVal_nil (env : envOf CType.denote ([] : List PType)) :
    CtxVal [] env ([] : Ctxt NatVar PType.denote) := by
  intro t v1 v2 hIn
  cases hIn

theorem ctxVal_extend {envT : List PType} {G : Ctxt NatVar PType.denote}
    (env : envOf CType.denote envT)
    (hCtx : CtxVal envT env G)
    {t : PType} (x : PType.denote t) :
    CtxVal (t :: envT) (x, env)
      (mkPair (v1 := (⟨envT.length⟩ : NatVar t)) (v2 := x) :: G) := by
  intro t' v1 v2 hIn
  rcases List.mem_cons.mp hIn with hHead | hTail
  · cases hHead
    refine ⟨by unfold Ok; simp [lookupType], ?_⟩
    simp [lookup]
  · rcases hCtx hTail with ⟨hOk, hVal⟩
    have hWeak : Ok (t :: envT) v1.idx t' :=
      ok_weaken (envT := envT) (n := v1.idx) (t := t') (t' := t) hOk
    refine ⟨hWeak, ?_⟩
    have hn : v1.idx ≠ envT.length := by
      intro hEqIdx
      have hOkLen : Ok envT envT.length t' := by
        simpa [hEqIdx] using hOk
      have hNone : lookupType envT envT.length = none := lookupType_length_none envT
      have hSome : lookupType envT envT.length = some t' := hOkLen
      have : (none : Option PType) = some t' := by
        simp [hNone] at hSome
      cases this
    have hTailOk : Ok envT v1.idx t' := by
      unfold Ok at hWeak ⊢
      simpa [hn] using hWeak
    have hProofEq :
        lookup envT v1.idx env (t := t')
          hTailOk =
        lookup envT v1.idx env (t := t') hOk := by
      exact lookup_proof_irrel (env := env)
        (h1 := hTailOk)
        (h2 := hOk)
    have hLookup :
        lookup (t :: envT) v1.idx (x, env) (t := t') hWeak =
          lookup envT v1.idx env (t := t') hOk := by
      simp [lookup, hn, hProofEq]
    exact hLookup.trans hVal

def CtxRel (envT : List PType) (env : envOf CType.denote envT)
    (G : Ctxt PType.denote NatVar) : Prop :=
  ∀ {t : PType} {v1 : PType.denote t} {v2 : NatVar t},
    mkPair v1 v2 ∈ G →
      ∃ h : Ok envT v2.idx t, lookup envT v2.idx env (t := t) h = v1

theorem ctxRel_nil (env : envOf CType.denote ([] : List PType)) :
    CtxRel [] env ([] : Ctxt PType.denote NatVar) := by
  intro t v1 v2 hIn
  cases hIn

theorem ctxRel_extend {envT : List PType} {G : Ctxt PType.denote NatVar}
    (env : envOf CType.denote envT)
    (hCtx : CtxRel envT env G)
    {t : PType} (x : PType.denote t) :
    CtxRel (t :: envT) (x, env)
      (mkPair (v1 := x) (v2 := (⟨envT.length⟩ : NatVar t)) :: G) := by
  intro t' v1 v2 hIn
  rcases List.mem_cons.mp hIn with hHead | hTail
  · cases hHead
    refine ⟨by unfold Ok; simp [lookupType], ?_⟩
    simp [lookup]
  · rcases hCtx hTail with ⟨hOk, hVal⟩
    have hWeak : Ok (t :: envT) v2.idx t' :=
      ok_weaken (envT := envT) (n := v2.idx) (t := t') (t' := t) hOk
    refine ⟨hWeak, ?_⟩
    have hn : v2.idx ≠ envT.length := by
      intro hEqIdx
      have hOkLen : Ok envT envT.length t' := by
        simpa [hEqIdx] using hOk
      have hNone : lookupType envT envT.length = none := lookupType_length_none envT
      have hSome : lookupType envT envT.length = some t' := hOkLen
      have : (none : Option PType) = some t' := by
        simp [hNone] at hSome
      cases this
    have hTailOk : Ok envT v2.idx t' := by
      unfold Ok at hWeak ⊢
      simpa [hn] using hWeak
    have hProofEq :
        lookup envT v2.idx env (t := t') hTailOk =
          lookup envT v2.idx env (t := t') hOk := by
      exact lookup_proof_irrel (env := env)
        (h1 := hTailOk)
        (h2 := hOk)
    have hLookup :
        lookup (t :: envT) v2.idx (x, env) (t := t') hWeak =
          lookup envT v2.idx env (t := t') hOk := by
      simp [lookup, hn, hProofEq]
    exact hLookup.trans hVal

theorem ctxRel_lookup {envT : List PType} {env : envOf CType.denote envT}
    {G : Ctxt PType.denote NatVar}
    (hCtx : CtxRel envT env G)
    {t : PType} {v1 : PType.denote t} {v2 : NatVar t}
    (hMem : mkPair v1 v2 ∈ G)
    (hOk : Ok envT v2.idx t) :
    lookup envT v2.idx env (t := t) hOk = v1 := by
  rcases hCtx hMem with ⟨hOk', hVal⟩
  calc
    lookup envT v2.idx env (t := t) hOk
        = lookup envT v2.idx env (t := t) hOk' := by
            exact lookup_proof_irrel (env := env) (h1 := hOk) (h2 := hOk')
    _ = v1 := hVal

theorem ctxOk_nil : CtxOk [] ([] : Ctxt NatVar UnitVar) := by
  intro t v1 v2 hIn
  cases hIn

theorem ctxOk_extend {envT : List PType} {G : Ctxt NatVar UnitVar} {t : PType}
    (hCtx : CtxOk envT G) :
  CtxOk (t :: envT)
      (mkPair (v1 := (⟨envT.length⟩ : NatVar t))
          (v2 := (PUnit.unit : UnitVar t)) :: G) := by
  intro t' v1 v2 hIn
  have hIn' := List.mem_cons.mp hIn
  rcases hIn' with hHead | hTail
  · cases hHead
    unfold Ok
    simp [lookupType]
  · exact ok_weaken (hCtx hTail)

theorem wfTerm_of_equiv :
    ∀ {result envT G} {e1 : PTerm NatVar result} {e2 : PTerm UnitVar result},
      PTermEquiv (result := result) (var1 := NatVar) (var2 := UnitVar) G e1 e2 →
      CtxOk envT G →
      WfTerm envT e1 := by
  intro result envT G e1 e2 hEq hCtx
  exact
    (PTermEquiv.rec
      (motive_1 := fun G e1 _e2 _hEq =>
        ∀ {envT : List PType}, CtxOk envT G → WfTerm envT e1)
      (motive_2 := fun G {t} p1 _p2 _hEq =>
        ∀ {envT : List PType}, CtxOk envT G → WfPrimop envT p1)
      (halt := by
        intro G v1 v2 hMem envT hCtx
        exact .halt (hCtx hMem))
      (app := by
        intro G t f1 f2 x1 x2 hMemF hMemX envT hCtx
        exact .app (hCtx hMemF) (hCtx hMemX))
      (bind := by
        intro G t p1 p2 e1 e2 hp he ihp ihe envT hCtx
        have hPrim : WfPrimop envT p1 := ihp hCtx
        have hCtx' :
            CtxOk (t :: envT)
              (mkPair (v1 := (⟨envT.length⟩ : NatVar t))
                  (v2 := (PUnit.unit : UnitVar t)) :: G) :=
          ctxOk_extend hCtx
        have hBody : WfTerm (t :: envT) (e1 ⟨envT.length⟩) :=
          ihe (⟨envT.length⟩) (PUnit.unit : UnitVar t) hCtx'
        exact .bind hPrim hBody)
      (var := by
        intro G t v1 v2 hMem envT hCtx
        exact .var (hCtx hMem))
      (tru := by
        intro G envT hCtx
        exact .tru)
      (fals := by
        intro G envT hCtx
        exact .fals)
      (pair := by
        intro G t1 t2 x1 x2 y1 y2 hMemX hMemY envT hCtx
        exact .pair (hCtx hMemX) (hCtx hMemY))
      (fst := by
        intro G t1 t2 x1 x2 hMem envT hCtx
        exact .fst (hCtx hMem))
      (snd := by
        intro G t1 t2 x1 x2 hMem envT hCtx
        exact .snd (hCtx hMem))
      (abs := by
        intro G t f1 f2 hEqBody ihBody envT hCtx
        have hCtx' :
            CtxOk (t :: envT)
              (mkPair (v1 := (⟨envT.length⟩ : NatVar t))
                  (v2 := (PUnit.unit : UnitVar t)) :: G) :=
          ctxOk_extend hCtx
        have hBody : WfTerm (t :: envT) (f1 ⟨envT.length⟩) :=
          ihBody (⟨envT.length⟩) (PUnit.unit : UnitVar t) hCtx'
        exact .abs hBody)
      hEq)
      hCtx

theorem ptermWf [PTermParametricity] :
  ∀ {result : PType} (E : PTermClosed result),
    WfTerm ([] : List PType) (E NatVar) := by
  intro result E
  have hEq :
      PTermEquiv (result := result) (var1 := NatVar) (var2 := UnitVar)
        ([] : Ctxt NatVar UnitVar) (E NatVar) (E UnitVar) :=
    ptermEquivClosed (E := E) (var1 := NatVar) (var2 := UnitVar)
  exact wfTerm_of_equiv (envT := []) hEq ctxOk_nil

theorem ccTerm_correct_of_equiv :
    ∀ {result G} {e1 : PTerm PType.denote result} {e2 : PTerm NatVar result},
      PTermEquiv (result := result) (var1 := PType.denote) (var2 := NatVar) G e1 e2 →
      ∀ {envT : List PType} (env : envOf CType.denote envT) (k : PType.denote result → Bool),
        (hWf : WfTerm envT e2) →
        CtxRel envT env G →
        PTerm.denote e1 k =
          CTerm.denote (CFuncs.denote (ccTerm CType.denote result e2 envT hWf) k env) k := by
  intro result G e1 e2 hEq
  exact
    (PTermEquiv.rec
      (motive_1 := fun G e1 e2 _hEq =>
        ∀ {envT : List PType} (env : envOf CType.denote envT) (k : PType.denote result → Bool),
          (hWf : WfTerm envT e2) →
          CtxRel envT env G →
          PTerm.denote e1 k =
            CTerm.denote (CFuncs.denote (ccTerm CType.denote result e2 envT hWf) k env) k)
      (motive_2 := fun G {t} p1 p2 _hEq =>
        ∀ {envT : List PType} (env : envOf CType.denote envT) (k : PType.denote result → Bool),
          (hWf : WfPrimop envT p2) →
          CtxRel envT env G →
          PPrimop.denote p1 k =
            CPrimops.denote
              (CFuncs.denote (ccPrimop CType.denote result t p2 envT hWf) k env))
      (halt := by
        intro G v1 v2 hMem envT env k hWf hCtx
        have hLookup :
            lookup envT v2.idx env (t := result) (wfTerm_halt_inv hWf) = v1 :=
          ctxRel_lookup (hCtx := hCtx) (hMem := hMem) (hOk := wfTerm_halt_inv hWf)
        simp [ccTerm, hLookup])
      (app := by
        intro G t f1 f2 x1 x2 hMemF hMemX envT env k hWf hCtx
        have hLookupF :
            lookup envT f2.idx env (t := .cont t) (wfTerm_app_inv hWf).1 = f1 :=
          ctxRel_lookup (hCtx := hCtx) (hMem := hMemF) (hOk := (wfTerm_app_inv hWf).1)
        have hLookupX :
            lookup envT x2.idx env (t := t) (wfTerm_app_inv hWf).2 = x1 :=
          ctxRel_lookup (hCtx := hCtx) (hMem := hMemX) (hOk := (wfTerm_app_inv hWf).2)
        simp [ccTerm, hLookupF, hLookupX])
      (bind := by
        intro G t p1 p2 e1 e2 hp he ihp ihe envT env k hWf hCtx
        have hBind := wfTerm_bind_inv hWf
        have hPrim :
            PPrimop.denote p1 k =
              CPrimops.denote
                (CFuncs.denote (ccPrimop CType.denote result t p2 envT hBind.1) k env) :=
          ihp env k hBind.1 hCtx
        have hCtx' :
            CtxRel (t :: envT) (PPrimop.denote p1 k, env)
              (mkPair (v1 := PPrimop.denote p1 k)
                  (v2 := (⟨envT.length⟩ : NatVar t)) :: G) :=
          ctxRel_extend env hCtx (x := PPrimop.denote p1 k)
        have hBody :
            PTerm.denote (e1 (PPrimop.denote p1 k)) k =
              CTerm.denote
                (CFuncs.denote
                  (ccTerm CType.denote result (e2 ⟨envT.length⟩) (t :: envT) hBind.2)
                  k
                  (PPrimop.denote p1 k, env))
                k :=
          by
            simpa using
              (@ihe (PPrimop.denote p1 k) (⟨envT.length⟩) (t :: envT)
                ((PPrimop.denote p1 k, env) : envOf CType.denote (t :: envT))
                k
                hBind.2
                hCtx')
        calc
          PTerm.denote (.bind p1 e1) k
              = PTerm.denote (e1 (PPrimop.denote p1 k)) k := by
                  simp
          _ = CTerm.denote
                (CFuncs.denote
                  (ccTerm CType.denote result (e2 ⟨envT.length⟩) (t :: envT) hBind.2)
                  k
                  (PPrimop.denote p1 k, env))
                k := hBody
          _ = CTerm.denote
                (CFuncs.denote (ccTerm CType.denote result (.bind p2 e2) envT hWf) k env)
                k := by
                  simp [ccTerm, spliceFuncs_correct, spliceTerm_correct, hPrim.symm])
      (var := by
        intro G t v1 v2 hMem envT env k hWf hCtx
        have hLookup :
            lookup envT v2.idx env (t := t) (wfPrimop_var_inv hWf) = v1 :=
          ctxRel_lookup (hCtx := hCtx) (hMem := hMem) (hOk := wfPrimop_var_inv hWf)
        simp [ccPrimop, hLookup])
      (tru := by
        intro G envT env k hWf hCtx
        simp [ccPrimop])
      (fals := by
        intro G envT env k hWf hCtx
        simp [ccPrimop])
      (pair := by
        intro G t1 t2 x1 x2 y1 y2 hMemX hMemY envT env k hWf hCtx
        have hLookupX :
            lookup envT x2.idx env (t := t1) (wfPrimop_pair_inv hWf).1 = x1 :=
          ctxRel_lookup (hCtx := hCtx) (hMem := hMemX) (hOk := (wfPrimop_pair_inv hWf).1)
        have hLookupY :
            lookup envT y2.idx env (t := t2) (wfPrimop_pair_inv hWf).2 = y1 :=
          ctxRel_lookup (hCtx := hCtx) (hMem := hMemY) (hOk := (wfPrimop_pair_inv hWf).2)
        simp [ccPrimop, hLookupX, hLookupY])
      (fst := by
        intro G t1 t2 x1 x2 hMem envT env k hWf hCtx
        have hLookup :
            lookup envT x2.idx env (t := .prod t1 t2) (wfPrimop_fst_inv hWf) = x1 :=
          ctxRel_lookup (hCtx := hCtx) (hMem := hMem) (hOk := wfPrimop_fst_inv hWf)
        simp [ccPrimop, hLookup])
      (snd := by
        intro G t1 t2 x1 x2 hMem envT env k hWf hCtx
        have hLookup :
            lookup envT x2.idx env (t := .prod t1 t2) (wfPrimop_snd_inv hWf) = x1 :=
          ctxRel_lookup (hCtx := hCtx) (hMem := hMem) (hOk := wfPrimop_snd_inv hWf)
        simp [ccPrimop, hLookup])
      (abs := by
        intro G t f1 f2 hEqBody ihBody envT env k hWf hCtx
        funext x
        have hBody :
            PTerm.denote (f1 x) k =
              CTerm.denote
                (CFuncs.denote
                  (ccTerm CType.denote result (f2 ⟨envT.length⟩) (t :: envT) (wfPrimop_abs_inv hWf))
                  k
                  (x, env))
                k := by
          have hCtx' :
              CtxRel (t :: envT) (x, env)
                (mkPair (v1 := x) (v2 := (⟨envT.length⟩ : NatVar t)) :: G) :=
            ctxRel_extend env hCtx (x := x)
          exact
            by
              simpa using
                (@ihBody x (⟨envT.length⟩) (t :: envT)
                  ((x, env) : envOf CType.denote (t :: envT))
                  k
                  (wfPrimop_abs_inv hWf)
                  hCtx')
        have hRhs :
            (CPrimops.denote
              (CFuncs.denote (ccPrimop CType.denote result (.cont t) (.abs f2) envT hWf) k env))
              x =
              CTerm.denote
                (CFuncs.denote
                  (ccTerm CType.denote result (f2 ⟨envT.length⟩) (t :: envT) (wfPrimop_abs_inv hWf))
                  k
                  (x, env))
                k := by
          calc
            (CPrimops.denote
              (CFuncs.denote (ccPrimop CType.denote result (.cont t) (.abs f2) envT hWf) k env))
              x
                = CTerm.denote
                    (unpackTerm envT (.ret (envPackVal envT env))
                      (fun env' =>
                        CFuncs.denote
                          (ccTerm CType.denote result (f2 ⟨envT.length⟩) (t :: envT)
                            (wfPrimop_abs_inv hWf))
                          k
                          (x, env')))
                    k := by
                      simp [ccPrimop, inside_correct, splicePrim_correct, packTerm_correct]
            _ = CTerm.denote
                  (CFuncs.denote
                    (ccTerm CType.denote result (f2 ⟨envT.length⟩) (t :: envT) (wfPrimop_abs_inv hWf))
                    k
                    (x, env))
                  k := by
                    calc
                      CTerm.denote
                        (unpackTerm envT (.ret (envPackVal envT env))
                          (fun env' =>
                            CFuncs.denote
                              (ccTerm CType.denote result (f2 ⟨envT.length⟩) (t :: envT)
                                (wfPrimop_abs_inv hWf))
                              k
                              (x, env')))
                        k
                          = CTerm.denote
                              ((fun env' =>
                                CFuncs.denote
                                  (ccTerm CType.denote result (f2 ⟨envT.length⟩) (t :: envT)
                                    (wfPrimop_abs_inv hWf))
                                  k
                                  (x, env'))
                                (envUnpackVal envT (envPackVal envT env)))
                              k := by
                                  simpa using unpackTerm_correct (result := result)
                                    (envT := envT)
                                    (ps := (.ret (envPackVal envT env)))
                                    (e := fun env' =>
                                      CFuncs.denote
                                        (ccTerm CType.denote result (f2 ⟨envT.length⟩) (t :: envT)
                                          (wfPrimop_abs_inv hWf))
                                        k
                                        (x, env'))
                                    (k := k)
                      _ = CTerm.denote
                            (CFuncs.denote
                              (ccTerm CType.denote result (f2 ⟨envT.length⟩) (t :: envT)
                                (wfPrimop_abs_inv hWf))
                              k
                              (x, env))
                            k := by
                              simp
        calc
          PPrimop.denote (.abs f1) k x = PTerm.denote (f1 x) k := rfl
          _ = CTerm.denote
                (CFuncs.denote
                  (ccTerm CType.denote result (f2 ⟨envT.length⟩) (t :: envT) (wfPrimop_abs_inv hWf))
                  k
                  (x, env))
                k := hBody
          _ = (CPrimops.denote
                (CFuncs.denote (ccPrimop CType.denote result (.cont t) (.abs f2) envT hWf) k env))
                x := hRhs.symm)
      hEq)

@[simp] def CcTerm [PTermParametricity] {result : PType}
    (E : PTermClosed result) : CProgClosed result :=
  fun var =>
    mapFuncs (fun f => f PUnit.unit)
      (ccTerm var result (E NatVar) [] (ptermWf E))

theorem CcTerm_correct [PTermParametricity] :
  ∀ {result : PType} (E : PTermClosed result) (k : PType.denote result → Bool),
    CProgClosed.denote (CcTerm E) k = PTermClosed.denote E k := by
  intro result E k
  have hEq :
      PTermEquiv (result := result) (var1 := PType.denote) (var2 := NatVar)
        ([] : Ctxt PType.denote NatVar) (E PType.denote) (E NatVar) :=
    ptermEquivClosed (E := E) (var1 := PType.denote) (var2 := NatVar)
  have hCtx :
      CtxRel ([] : List PType) (PUnit.unit : envOf CType.denote [])
        ([] : Ctxt PType.denote NatVar) :=
    ctxRel_nil (env := (PUnit.unit : envOf CType.denote []))
  have hMain :
      PTerm.denote (E PType.denote) k =
        CTerm.denote
          (CFuncs.denote (ccTerm CType.denote result (E NatVar) [] (ptermWf E)) k
            (PUnit.unit : envOf CType.denote []))
          k :=
    ccTerm_correct_of_equiv (e1 := E PType.denote) (e2 := E NatVar) hEq
      (envT := [])
      (env := (PUnit.unit : envOf CType.denote []))
      (k := k)
      (hWf := ptermWf E)
      hCtx
  calc
    CProgClosed.denote (CcTerm E) k
        = CTerm.denote
            ((CFuncs.denote (ccTerm CType.denote result (E NatVar) [] (ptermWf E)) k)
              (PUnit.unit : envOf CType.denote []))
            k := by
                simp [CcTerm, CProgClosed.denote, CProg.denote, mapFuncs_correct]
    _ = PTerm.denote (E PType.denote) k := by
          simpa using hMain.symm
    _ = PTermClosed.denote E k := by
          simp [PTermClosed.denote]

end LeanCompiler.STLC.CCify
