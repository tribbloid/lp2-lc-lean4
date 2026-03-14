import LeanCompiler.STLC.Source
import LeanCompiler.STLC.CPS

namespace LeanCompiler.STLC.CPSify

open LeanCompiler.STLC.Source
open LeanCompiler.STLC.CPS

@[simp] def cpsType : Ty → PType
  | .bool => .bool
  | .arrow t1 t2 => .cont (.prod (cpsType t1) (.cont (cpsType t2)))

mutual
  @[simp] def splice {var : PType → Type} {result1 result2 : PType} :
      PTerm var result1 → (var result1 → PTerm var result2) → PTerm var result2
    | .halt v, e2 => e2 v
    | .app f x, _ => .app f x
    | .bind p e, e2 => .bind (splicePrim p e2) (fun x => splice (e x) e2)

  @[simp] def splicePrim {var : PType → Type} {result1 result2 : PType} {t : PType} :
      PPrimop var result1 t → (var result1 → PTerm var result2) → PPrimop var result2 t
    | .var v, _ => .var v
    | .tru, _ => .tru
    | .fals, _ => .fals
    | .abs e, e2 => .abs (fun x => splice (e x) e2)
    | .pair v1 v2, _ => .pair v1 v2
    | .fst v, _ => .fst v
    | .snd v, _ => .snd v
end

@[simp] def cpsTerm {var : PType → Type} :
    {t : Ty} → Term (fun t => var (cpsType t)) t → PTerm var (cpsType t)
  | _, .var v => .halt v
  | _, .tru => .bind .tru (fun x => .halt x)
  | _, .fals => .bind .fals (fun x => .halt x)
  | _, .app e1 e2 =>
      splice (cpsTerm e1) (fun f =>
        splice (cpsTerm e2) (fun x =>
          .bind (.abs (fun r => .halt r)) (fun k =>
            .bind (.pair x k) (fun p =>
              .app f p))))
  | _, .abs e =>
      .bind (.abs (fun p =>
        .bind (.fst p) (fun x =>
          .bind (.snd p) (fun k =>
            splice (cpsTerm (e x)) (fun r => .app k r))))) (fun f =>
        .halt f)

abbrev CpsTerm {t : Ty} (E : TermClosed t) : PTermClosed (cpsType t) :=
  fun var => cpsTerm (var := var) (E (fun s => var (cpsType s)))

@[simp] def LR : (t : Ty) → Ty.denote t → PType.denote (cpsType t) → Prop
  | .bool, n1, n2 => n1 = n2
  | .arrow t1 t2, f1, f2 =>
      ∀ x1 x2, LR t1 x1 x2 →
        ∀ k, ∃ r,
          f2 (x2, k) = k r ∧
          LR t2 (f1 x1) r

abbrev CVar (t : Ty) : Type := PType.denote (cpsType t)

theorem splice_correct :
  ∀ {result1 result2 : PType}
    (e1 : PTerm PType.denote result1)
    (e2 : PType.denote result1 → PTerm PType.denote result2)
    (k : PType.denote result2 → Bool),
    PTerm.denote (splice e1 e2) k =
      PTerm.denote e1 (fun r => PTerm.denote (e2 r) k) := by
  intro result1 result2 e1 e2 k
  let motiveTerm : PTerm PType.denote result1 → Prop :=
    fun e =>
      ∀ {result2 : PType}
        (e2 : PType.denote result1 → PTerm PType.denote result2)
        (k : PType.denote result2 → Bool),
        PTerm.denote (splice e e2) k =
          PTerm.denote e (fun r => PTerm.denote (e2 r) k)
  let motivePrim : (t : PType) → PPrimop PType.denote result1 t → Prop :=
    fun _ p =>
      ∀ {result2 : PType}
        (e2 : PType.denote result1 → PTerm PType.denote result2)
        (k : PType.denote result2 → Bool),
        PPrimop.denote (splicePrim p e2) k =
          PPrimop.denote p (fun r => PTerm.denote (e2 r) k)
  exact
    (PTerm.rec
      (motive_1 := motiveTerm)
      (motive_2 := motivePrim)
      (fun v => by
        intro result2 e2 k
        rfl)
      (fun f x => by
        intro result2 e2 k
        rfl)
      (fun p e ihp ihe => by
        intro result2 e2 k
        have hPrim := ihp (result2 := result2) e2 k
        have hBody := ihe (PPrimop.denote p (fun r => PTerm.denote (e2 r) k)) (result2 := result2) e2 k
        simpa [splice, hPrim] using hBody)
      (fun v => by
        intro result2 e2 k
        rfl)
      (by
        intro result2 e2 k
        rfl)
      (by
        intro result2 e2 k
        rfl)
      (fun e ihe => by
        intro result2 e2 k
        funext x
        simpa [splicePrim] using ihe x (result2 := result2) e2 k)
      (fun x y => by
        intro result2 e2 k
        rfl)
      (fun x => by
        intro result2 e2 k
        rfl)
      (fun x => by
        intro result2 e2 k
        rfl)
      e1)
      (e2 := e2) (k := k)

theorem cpsTerm_correct_of_equiv :
    ∀ {t : Ty} {G : Source.Ctxt Ty.denote CVar}
      {e1 : Term Ty.denote t} {e2 : Term CVar t},
      TermEquiv (var1 := Ty.denote) (var2 := CVar) G e1 e2 →
      (∀ {t : Ty} {v1 : Ty.denote t} {v2 : CVar t},
        Source.mkPair v1 v2 ∈ G → LR t v1 v2) →
      ∀ k, ∃ r,
        PTerm.denote (cpsTerm (var := PType.denote) e2) k = k r ∧
        LR t (Term.denote e1) r := by
  intro t G e1 e2 hEq
  induction hEq
  case var G' t' v1 v2 hMem =>
    intro hRel k
    refine ⟨v2, ?_, ?_⟩
    · simp [cpsTerm]
    · exact hRel hMem
  case tru G' =>
    intro hRel k
    refine ⟨true, ?_, ?_⟩
    · simp [cpsTerm]
    · simp [LR]
  case fals G' =>
    intro hRel k
    refine ⟨false, ?_, ?_⟩
    · simp [cpsTerm]
    · simp [LR]
  case app G' t1 t2 f1 x1 f2 x2 hEqf hEqx ihf ihx =>
    intro hRel k
    let kf : PType.denote (cpsType (t1 ==> t2)) → Bool :=
      fun f => PTerm.denote (cpsTerm (var := PType.denote) x2) (fun x => f (x, fun r => k r))
    rcases ihf hRel kf with ⟨rf, hrf, hLRf⟩
    rcases ihx hRel (fun x => rf (x, fun r => k r)) with ⟨rx, hrx, hLRx⟩
    rcases hLRf (Term.denote x1) rx hLRx (fun r => k r) with ⟨r, hrfRun, hLR⟩
    refine ⟨r, ?_, hLR⟩
    calc
      PTerm.denote (cpsTerm (var := PType.denote) (.app f2 x2)) k
          = PTerm.denote (cpsTerm (var := PType.denote) f2)
              (fun f => PTerm.denote (cpsTerm (var := PType.denote) x2) (fun x => f (x, fun r => k r))) := by
                simp [cpsTerm, splice_correct]
      _ = PTerm.denote (cpsTerm (var := PType.denote) x2) (fun x => rf (x, fun r => k r)) := by
            simpa [kf] using hrf
      _ = rf (rx, fun r => k r) := by
            simpa using hrx
      _ = k r := hrfRun
  case abs G' t1 t2 f1 f2 hEqBody ihBody =>
    intro hRel k
    let rf : PType.denote (cpsType (t1 ==> t2)) :=
      fun p => PTerm.denote (cpsTerm (var := PType.denote) (f2 p.1)) (fun r => p.2 r)
    refine ⟨rf, ?_, ?_⟩
    · simp [cpsTerm, splice_correct, rf]
    · intro x1 x2 hLRx k2
      have hRel' :
          ∀ {t : Ty} {v1 : Ty.denote t} {v2 : CVar t},
            Source.mkPair v1 v2 ∈ (Source.mkPair x1 x2 :: G') → LR t v1 v2 := by
        intro t v1 v2 hIn
        rcases List.mem_cons.mp hIn with hHead | hTail
        · cases hHead
          simpa using hLRx
        · exact hRel hTail
      rcases ihBody x1 x2 hRel' k2 with ⟨r2, hRun, hLR2⟩
      refine ⟨r2, ?_, hLR2⟩
      simpa [rf] using hRun

theorem CpsTerm_correct [TermParametricity] :
  ∀ {t : Ty} (E : TermClosed t) (k : PType.denote (cpsType t) → Bool),
    ∃ r,
      PTermClosed.denote (CpsTerm E) k = k r ∧
      LR t (TermClosed.denote E) r := by
  intro t E k
  have hEq :
      TermEquiv (var1 := Ty.denote) (var2 := CVar)
        ([] : Source.Ctxt Ty.denote CVar) (E Ty.denote) (E CVar) :=
    termEquivClosed (E := E) (var1 := Ty.denote) (var2 := CVar)
  have hRelNil :
      ∀ {t : Ty} {v1 : Ty.denote t} {v2 : CVar t},
        Source.mkPair v1 v2 ∈ ([] : Source.Ctxt Ty.denote CVar) → LR t v1 v2 := by
    intro t v1 v2 hIn
    cases hIn
  simpa [PTermClosed.denote, CpsTerm, TermClosed.denote]
    using cpsTerm_correct_of_equiv (e1 := E Ty.denote) (e2 := E CVar) hEq hRelNil k

theorem CpsTerm_correct_bool [TermParametricity] :
  ∀ (E : TermClosed .bool) (k : Bool → Bool),
    PTermClosed.denote (CpsTerm E) k = k (TermClosed.denote E) := by
  intro E k
  rcases CpsTerm_correct (E := E) (k := k) with ⟨r, hk, hrel⟩
  simp [LR] at hrel
  simpa [hrel] using hk

end LeanCompiler.STLC.CPSify
