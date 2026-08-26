import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace Umbral

structure TypeWithSafey {refs} [build : BuildEnv refs]
    (trm : ∀ {B : UIdU}, AST.Trm { F := refs.uid2val.UId, B := B, D := refs.D }) where
  t2 : AST.Typ build.BuildParameters
  safety : [_exe : ExeEnv refs] -> Safety trm t2

class ProvingEnv (refs : ExeRefs) extends BuildEnv refs where
  uid2typWithSafetyCtx := --TODO: this impl should be final, move into namespace
    toBuildEnv.uid2typCtx.mkLesser
      (λ _v => PSigma (λ (trm : ∀ {B : UIdU}, AST.Trm { F := refs.uid2val.UId, B := B, D := refs.D }) =>
        TypeWithSafey trm))

namespace ProvingEnv


end ProvingEnv

/-- Type syntax is independent of every free, bound, and data carrier map. -/
private theorem recarrierTypEq {refs : ExeRefs} [build : BuildEnv refs]
    {P : Parameters} (self : AST.Typ P)
    (leftF rightF : P.F → build.BuildParameters.F)
    (leftB rightB : P.B → build.BuildParameters.F ⊕ build.BuildParameters.B)
    (leftD rightD : P.D → build.BuildParameters.D) :
    self.recarrier leftF leftB leftD = self.recarrier rightF rightB rightD :=
  match self with
  | .primitive => rfl
  | .fn tIn tOut => by
    simp only [AST.recarrier]
    rw [recarrierTypEq tIn leftF rightF leftB rightB leftD rightD,
      recarrierTypEq tOut leftF rightF leftB rightB leftD rightD]




/-- Pointwise-equal carrier maps rebuild identical syntax. -/
private theorem recarrierCongr {P Q : Parameters} {l : Label} (self : AST P l)
    (leftF rightF : P.F → Q.F) (leftB rightB : P.B → Q.F ⊕ Q.B)
    (leftD rightD : P.D → Q.D)
    (hFree : ∀ free, leftF free = rightF free)
    (hBound : ∀ bound, leftB bound = rightB bound)
    (hData : ∀ repr, leftD repr = rightD repr) :
    self.recarrier leftF leftB leftD = self.recarrier rightF rightB rightD := by
  have hFreeMap := funext hFree
  have hBoundMap := funext hBound
  have hDataMap := funext hData
  subst rightF
  subst rightB
  subst rightD
  rfl

/-- Consecutive carrier changes compose without changing structural binder slots. -/
@[simp]
private theorem recarrierComp {P Q R : Parameters} {l : Label} (self : AST P l)
    (firstF : P.F → Q.F) (firstB : P.B → Q.F ⊕ Q.B) (firstD : P.D → Q.D)
    (secondF : Q.F → R.F) (secondB : Q.B → R.F ⊕ R.B) (secondD : Q.D → R.D) :
    (self.recarrier firstF firstB firstD).recarrier secondF secondB secondD =
      self.recarrier
        (λ free => secondF (firstF free))
        (λ bound =>
          match firstB bound with
          | .inl free => .inl (secondF free)
          | .inr target => secondB target)
        (λ repr => secondD (firstD repr)) := by
  induction self generalizing Q R with
  | primitive => rfl
  | fn tIn tOut ihIn ihOut => simp [AST.recarrier, ihIn, ihOut]
  | val value ih => simp [AST.recarrier, ih]
  | apply fnTerm arg ihFn ihArg => simp [AST.recarrier, ihFn, ihArg]
  | ref source =>
    cases source with
    | inl free => rfl
    | inr bound => cases h : firstB bound <;> simp [AST.recarrier, h]
  | lit repr => rfl
  | lam body tIn ihBody ihIn =>
    simp [AST.recarrier, ihBody, ihIn]
    congr 1
    funext bound
    cases bound with
    | inl outer =>
      cases hFirst : firstB outer with
      | inl free => simp [hFirst]
      | inr target =>
        cases hSecond : secondB target <;> simp [hFirst, hSecond]
    | inr newest => cases newest; rfl

/-- A mapped successful outcome exposes the successful source outcome. -/
private theorem outcomeMapYield {T T2 : Type 2} (self : Rec.Outcome T)
    (map : T → T2) (result : T2) (hResult : self.map map = .yield result) :
    ∃ source, self = .yield source ∧ map source = result := by
  cases self with
  | outOfFuel => cases hResult
  | yield source => exact ⟨source, rfl, Rec.Outcome.yield.inj hResult⟩

/-- Successful lambda inference exposes successful inference of its instantiated body. -/
private theorem lamInferInv {refs : ExeRefs} [build : BuildEnv refs]
    (body : AST {build.BuildParameters with B := build.BuildParameters.B ⊕ Unit} .trm)
    (tIn typ : AST.Typ build.BuildParameters)
    (hInfer : ∃ fuel, (AST.val (.lam body tIn) : AST.Trm build.BuildParameters).inferCore
      fuel = .yield (some typ)) :
    ∃ fuel tOut,
      (body.instantiateLamBody (build.uid2typCtx.inv tIn)).inferCore fuel =
        .yield (some tOut) ∧
      typ = .fn tIn tOut := by
  rcases hInfer with ⟨fuel, hInfer⟩
  cases fuel with
  | zero => simp [AST.inferCore] at hInfer
  | succ fuel =>
    simp only [AST.inferCore] at hInfer
    have hMapped := outcomeMapYield
      ((body.instantiateLamBody (build.uid2typCtx.inv tIn)).inferCore fuel)
      (λ out => out.map (λ tOut => AST.fn tIn tOut)) (some typ) hInfer
    rcases hMapped with ⟨bodyResult, hBody, hType⟩
    cases bodyResult with
    | none => cases hType
    | some tOut => exact ⟨fuel, tOut, hBody, (Option.some.inj hType).symm⟩

/-- Successful instantiated-body inference reconstructs successful lambda inference. -/
private theorem lamInferIntro {refs : ExeRefs} [build : BuildEnv refs]
    (body : AST {build.BuildParameters with B := build.BuildParameters.B ⊕ Unit} .trm)
    (tIn tOut : AST.Typ build.BuildParameters) (fuel : Nat)
    (hBody : (body.instantiateLamBody (build.uid2typCtx.inv tIn)).inferCore fuel =
      .yield (some tOut)) :
    (AST.val (.lam body tIn) : AST.Trm build.BuildParameters).inferCore (fuel + 1) =
      .yield (some (.fn tIn tOut)) := by
  have hMapped := congrArg
    (λ result => result.map (λ out => out.map (λ bodyType => AST.fn tIn bodyType)))
    hBody
  simpa only [AST.inferCore, AST.instantiateLamBody, Rec.Outcome.map,
    Option.map] using hMapped

/-- Recarried lambda inference exposes the normalized compiler body. -/
private theorem recarrierLamInferInv {refs : ExeRefs} [build : BuildEnv refs]
    {P : Parameters}
    (body : AST {P with B := P.B ⊕ Unit} .trm) (tIn : AST.Typ P)
    (mapF : P.F → build.BuildParameters.F)
    (mapB : P.B → build.BuildParameters.F ⊕ build.BuildParameters.B)
    (mapD : P.D → build.BuildParameters.D) (typ : AST.Typ build.BuildParameters)
    (hInfer : ∃ fuel,
      (AST.val ((AST.lam body tIn).recarrier mapF mapB mapD) :
        AST.Trm build.BuildParameters).inferCore fuel = .yield (some typ)) :
    ∃ fuel tOut,
      (body.recarrier mapF
        (λ bound =>
          match bound with
          | .inl outer => mapB outer
          | .inr () => .inr (build.uid2typCtx.inv
            (tIn.recarrier mapF mapB mapD)))
        mapD).inferCore fuel = .yield (some tOut) ∧
      typ = .fn (tIn.recarrier mapF mapB mapD) tOut := by
  cases hCarried : (AST.lam body tIn).recarrier mapF mapB mapD with
  | lit repr => simp [AST.recarrier] at hCarried
  | lam carriedBody carriedInput =>
    rw [hCarried] at hInfer
    simp only [AST.recarrier] at hCarried
    have hBodyCarrier := (AST.lam.inj hCarried).1
    have hInputCarrier := (AST.lam.inj hCarried).2
    rcases lamInferInv (build := build) carriedBody carriedInput typ hInfer with
      ⟨fuel, tOut, hBody, hType⟩
    refine ⟨fuel, tOut, ?_, ?_⟩
    rw [← hBodyCarrier, ← hInputCarrier] at hBody
    simp only [AST.instantiateLamBody, recarrierComp, id_eq] at hBody
    rw [← hBody]
    apply congrArg (λ term : AST.Trm build.BuildParameters => term.inferCore fuel)
    apply recarrierCongr
    · intro free
      rfl
    · intro bound
      cases bound with
      | inl outer => cases h : mapB outer <;> simp [h]
      | inr newest => cases newest; rfl
    · intro repr
      rfl
    simpa only [hInputCarrier] using hType

/-- Normalized compiler-body inference reconstructs recarried lambda inference. -/
private theorem recarrierLamInferIntro {refs : ExeRefs} [build : BuildEnv refs]
    {P : Parameters}
    (body : AST {P with B := P.B ⊕ Unit} .trm) (tIn : AST.Typ P)
    (mapF : P.F → build.BuildParameters.F)
    (mapB : P.B → build.BuildParameters.F ⊕ build.BuildParameters.B)
    (mapD : P.D → build.BuildParameters.D) (tOut : AST.Typ build.BuildParameters)
    (fuel : Nat)
    (hBody : (body.recarrier mapF
      (λ bound =>
        match bound with
        | .inl outer => mapB outer
        | .inr () => .inr (build.uid2typCtx.inv
          (tIn.recarrier mapF mapB mapD)))
      mapD).inferCore fuel = .yield (some tOut)) :
    (AST.val ((AST.lam body tIn).recarrier mapF mapB mapD) :
      AST.Trm build.BuildParameters).inferCore (fuel + 1) =
        .yield (some (.fn (tIn.recarrier mapF mapB mapD) tOut)) := by
  cases hCarried : (AST.lam body tIn).recarrier mapF mapB mapD with
  | lit repr => simp [AST.recarrier] at hCarried
  | lam carriedBody carriedInput =>
    simp only [AST.recarrier] at hCarried
    have hBodyCarrier := (AST.lam.inj hCarried).1
    have hInputCarrier := (AST.lam.inj hCarried).2
    have hInstantiated :
        (carriedBody.instantiateLamBody
          (build.uid2typCtx.inv carriedInput)).inferCore fuel =
            .yield (some tOut) := by
      rw [← hBodyCarrier, ← hInputCarrier]
      simp only [AST.instantiateLamBody, recarrierComp, id_eq]
      rw [← hBody]
      apply congrArg (λ term : AST.Trm build.BuildParameters => term.inferCore fuel)
      apply recarrierCongr
      · intro free
        rfl
      · intro bound
        cases bound with
        | inl outer => cases h : mapB outer <;> simp [h]
        | inr newest => cases newest; rfl
      · intro repr
        rfl
    have hInfer := lamInferIntro (build := build) carriedBody carriedInput tOut
      fuel hInstantiated
    rw [hInputCarrier]
    exact hInfer

mutual

  private theorem recarrierValInfer {refs : ExeRefs} [build : BuildEnv refs]
      {P : Parameters} (self : AST.Val P)
      (leftF rightF : P.F → build.BuildParameters.F)
      (leftB rightB : P.B → build.BuildParameters.F ⊕ build.BuildParameters.B)
      (leftD rightD : P.D → build.BuildParameters.D)
      (hFree : ∀ (free : P.F) (typ : AST.Typ build.BuildParameters),
        (∃ fuel, (AST.ref (.inl (leftF free)) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ)) →
        ∃ fuel, (AST.ref (.inl (rightF free)) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ))
      (hBound : ∀ (bound : P.B) (typ : AST.Typ build.BuildParameters),
        (∃ fuel, (AST.ref (leftB bound) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ)) →
        ∃ fuel, (AST.ref (rightB bound) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ))
      (typ : AST.Typ build.BuildParameters)
      (hInfer : ∃ fuel,
        (AST.val (self.recarrier leftF leftB leftD)).inferCore fuel = .yield (some typ)) :
      ∃ fuel, (AST.val (self.recarrier rightF rightB rightD)).inferCore fuel =
        .yield (some typ) := by
    cases self with
    | lit repr =>
      rcases hInfer with ⟨fuel, hInfer⟩
      cases fuel with
      | zero => simp [AST.inferCore] at hInfer
      | succ fuel =>
        have hType : (AST.primitive : AST.Typ build.BuildParameters) = typ := by
          simpa [AST.inferCore] using hInfer
        subst typ
        exact ⟨1, rfl⟩
    | lam body tIn =>
      rcases recarrierLamInferInv body tIn leftF leftB leftD typ hInfer with
        ⟨fuel, bodyType, hBody, hType⟩
      subst typ
      let leftBodyB : P.B ⊕ Unit →
          build.BuildParameters.F ⊕ build.BuildParameters.B :=
        λ bound =>
          match bound with
          | .inl outer => leftB outer
          | .inr () => .inr (build.uid2typCtx.inv
            (tIn.recarrier leftF leftB leftD))
      have hInputType := recarrierTypEq tIn leftF rightF leftB rightB
        leftD rightD
      let rightBodyB : P.B ⊕ Unit →
          build.BuildParameters.F ⊕ build.BuildParameters.B :=
        λ bound =>
          match bound with
          | .inl outer => rightB outer
          | .inr () => .inr (build.uid2typCtx.inv
            (tIn.recarrier rightF rightB rightD))
      have hIndex :
          build.uid2typCtx.inv (tIn.recarrier leftF leftB leftD) =
            build.uid2typCtx.inv (tIn.recarrier rightF rightB rightD) :=
        congrArg build.uid2typCtx.inv hInputType
      have hNestedBound :
          ∀ (bound : P.B ⊕ Unit) (refType : AST.Typ build.BuildParameters),
            (∃ refFuel,
              (AST.ref (leftBodyB bound) : AST.Trm build.BuildParameters).inferCore
                refFuel = .yield (some refType)) →
            ∃ refFuel,
              (AST.ref (rightBodyB bound) : AST.Trm build.BuildParameters).inferCore
                refFuel = .yield (some refType) := by
        intro bound refType hRef
        cases bound with
        | inl outer => exact hBound outer refType hRef
        | inr newest =>
          cases newest
          simpa only [leftBodyB, rightBodyB, hIndex] using hRef
      have hRightBody := recarrierTrmInfer body leftF rightF leftBodyB
        rightBodyB leftD rightD hFree hNestedBound bodyType
        ⟨fuel, hBody⟩
      rcases hRightBody with ⟨rightFuel, hRightBody⟩
      refine ⟨rightFuel + 1, ?_⟩
      rw [hInputType]
      simpa only [rightBodyB] using recarrierLamInferIntro body tIn rightF
        rightB rightD bodyType rightFuel hRightBody

  private theorem recarrierTrmInfer {refs : ExeRefs} [build : BuildEnv refs]
      {P : Parameters} (self : AST.Trm P)
      (leftF rightF : P.F → build.BuildParameters.F)
      (leftB rightB : P.B → build.BuildParameters.F ⊕ build.BuildParameters.B)
      (leftD rightD : P.D → build.BuildParameters.D)
      (hFree : ∀ (free : P.F) (typ : AST.Typ build.BuildParameters),
        (∃ fuel, (AST.ref (.inl (leftF free)) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ)) →
        ∃ fuel, (AST.ref (.inl (rightF free)) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ))
      (hBound : ∀ (bound : P.B) (typ : AST.Typ build.BuildParameters),
        (∃ fuel, (AST.ref (leftB bound) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ)) →
        ∃ fuel, (AST.ref (rightB bound) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ))
      (typ : AST.Typ build.BuildParameters)
      (hInfer : ∃ fuel,
        (self.recarrier leftF leftB leftD).inferCore fuel = .yield (some typ)) :
      ∃ fuel, (self.recarrier rightF rightB rightD).inferCore fuel = .yield (some typ) := by
    cases self with
    | val value =>
      exact recarrierValInfer value leftF rightF leftB rightB leftD rightD
        hFree hBound typ hInfer
    | ref source =>
      cases source with
      | inl free => exact hFree free typ hInfer
      | inr bound => exact hBound bound typ hInfer
    | apply fnTerm arg =>
      rcases hInfer with ⟨fuel, hInfer⟩
      cases fuel with
      | zero => simp [AST.inferCore] at hInfer
      | succ fuel =>
        let leftFn := fnTerm.recarrier leftF leftB leftD
        let rightFn := fnTerm.recarrier rightF rightB rightD
        let leftArg := arg.recarrier leftF leftB leftD
        let rightArg := arg.recarrier rightF rightB rightD
        cases hFn : leftFn.inferCore fuel with
        | outOfFuel => simp [AST.inferCore, leftFn, hFn] at hInfer
        | yield fnResult =>
          cases hArg : leftArg.inferCore fuel with
          | outOfFuel => simp [AST.inferCore, leftFn, leftArg, hFn, hArg] at hInfer
          | yield argResult =>
            cases fnResult with
            | none => simp [AST.inferCore, leftFn, leftArg, hFn, hArg] at hInfer
            | some fnType =>
              cases fnType with
              | primitive => simp [AST.inferCore, leftFn, leftArg, hFn, hArg] at hInfer
              | fn tIn tOut =>
                cases argResult with
                | none => simp [AST.inferCore, leftFn, leftArg, hFn, hArg] at hInfer
                | some argType =>
                  by_cases hSubtype : argType ≤ tIn
                  · have hType : tOut = typ := by
                      simpa [AST.inferCore, leftFn, leftArg, hFn, hArg, hSubtype] using hInfer
                    subst typ
                    have hRightFn := recarrierTrmInfer fnTerm leftF rightF leftB rightB
                      leftD rightD hFree hBound (.fn tIn tOut) ⟨fuel, hFn⟩
                    have hRightArg := recarrierTrmInfer arg leftF rightF leftB rightB
                      leftD rightD hFree hBound argType ⟨fuel, hArg⟩
                    rcases hRightFn with ⟨fnFuel, hRightFn⟩
                    rcases hRightArg with ⟨argFuel, hRightArg⟩
                    let combined := max fnFuel argFuel
                    have hFnTop := rightFn.termInferMonotone fnFuel combined
                      (.some (.fn tIn tOut)) (Nat.le_max_left _ _) hRightFn
                    have hArgTop := rightArg.termInferMonotone argFuel combined
                      (.some argType) (Nat.le_max_right _ _) hRightArg
                    refine ⟨combined + 1, ?_⟩
                    simp [AST.inferCore, rightFn, rightArg, hFnTop, hArgTop, hSubtype]
                  · simp [AST.inferCore, leftFn, leftArg, hFn, hArg, hSubtype] at hInfer

end

/-- Successful application inference exposes the function and argument premises. -/
private theorem applyInferInv {refs : ExeRefs} [build : BuildEnv refs]
    (fnTerm arg : AST.Trm refs.ExeParameters) (typ : AST.Typ build.BuildParameters)
    (hInfer : ∃ inferFuel,
      (AST.apply fnTerm arg).infer inferFuel = .yield (some typ)) :
    ∃ inferFuel tIn tOut,
      fnTerm.infer inferFuel = .yield (some (.fn tIn tOut)) ∧
      arg.infer inferFuel = .yield (some tIn) ∧ typ = tOut := by
  rcases hInfer with ⟨inferFuel, hInfer⟩
  cases inferFuel with
  | zero => simp [AST.infer, AST.inferCore] at hInfer
  | succ inferFuel =>
    let buildFn := fnTerm.exe2build
    let buildArg := arg.exe2build
    have hCore : (AST.apply buildFn buildArg).inferCore (inferFuel + 1) =
        .yield (some typ) := by
      simpa [AST.infer, AST.exe2build, AST.recarrier, buildFn, buildArg] using hInfer
    cases hFn : buildFn.inferCore inferFuel with
    | outOfFuel => simp [AST.inferCore, hFn] at hCore
    | yield fnResult =>
      cases hArg : buildArg.inferCore inferFuel with
      | outOfFuel => simp [AST.inferCore, hFn, hArg] at hCore
      | yield argResult =>
        cases fnResult with
        | none => simp [AST.inferCore, hFn, hArg] at hCore
        | some fnType =>
          cases fnType with
          | primitive => simp [AST.inferCore, hFn, hArg] at hCore
          | fn tIn tOut =>
            cases argResult with
            | none => simp [AST.inferCore, hFn, hArg] at hCore
            | some argType =>
              by_cases hSubtype : argType ≤ tIn
              · have hType : tOut = typ := by
                  simpa [AST.inferCore, hFn, hArg, hSubtype] using hCore
                have hArgType : argType = tIn := hSubtype
                subst argType
                subst typ
                exact ⟨inferFuel, tIn, tOut, by simpa [AST.infer, buildFn] using hFn,
                  by simpa [AST.infer, buildArg] using hArg, rfl⟩
              · simp [AST.inferCore, hFn, hArg, hSubtype] at hCore

/-- Inference of an executable reference exposes inference of its stored value. -/
private theorem referenceInferInv {refs : ExeRefs} [build : BuildEnv refs]
    (receipt : refs.uid2val.UId) (typ : AST.Typ build.BuildParameters)
    (hInfer : ∃ inferFuel,
      (AST.ref (.inl receipt) : AST.Trm refs.ExeParameters).infer inferFuel =
        .yield (some typ)) :
    ∃ inferFuel, (refs.uid2val.get receipt).asTrm.infer inferFuel =
      .yield (some typ) := by
  rcases hInfer with ⟨inferFuel, hInfer⟩
  cases inferFuel with
  | zero => simp [AST.infer, AST.inferCore] at hInfer
  | succ inferFuel =>
    exact ⟨inferFuel, by
      simpa [AST.infer, AST.exe2build, AST.inferCore] using hInfer⟩

/-- A primitive value cannot infer a function type. -/
private theorem literalNotFunction {refs : ExeRefs} [build : BuildEnv refs]
    (repr : refs.D) (tIn tOut : AST.Typ build.BuildParameters)
    (hInfer : ∃ inferFuel,
      (AST.val (.lit repr) : AST.Trm refs.ExeParameters).infer inferFuel =
        .yield (some (.fn tIn tOut))) : False := by
  rcases hInfer with ⟨inferFuel, hInfer⟩
  cases inferFuel with
  | zero => simp [AST.infer, AST.inferCore] at hInfer
  | succ inferFuel => simp [AST.infer, AST.exe2build, AST.inferCore] at hInfer

/-- Structural lambda inference is preserved when the compiler slot is beta-instantiated. -/
private theorem betaInfer {refs : ExeRefs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (body : AST {refs.ExeParameters with B := refs.ExeParameters.B ⊕ Unit} .trm)
    (tIn : AST.Typ refs.ExeParameters) (input : AST.Val refs.ExeParameters)
    (compileIn compileOut : AST.Typ build.BuildParameters)
    (hLam : ∃ inferFuel,
      (AST.val (.lam body tIn) : AST.Trm refs.ExeParameters).infer inferFuel =
        .yield (some (.fn compileIn compileOut)))
    (hInput : ∃ inferFuel, input.asTrm.infer inferFuel =
      .yield (some compileIn)) :
    ∃ inferFuel,
      (body.instantiateLamBody (exe.uid2valCtx.inv input)).infer inferFuel =
        .yield (some compileOut) := by
  have hLamCore : ∃ inferFuel,
      (AST.val ((AST.lam body tIn).recarrier id Sum.inl id) :
        AST.Trm build.BuildParameters).inferCore inferFuel =
          .yield (some (.fn compileIn compileOut)) := by
    simpa only [AST.infer, AST.exe2build, AST.recarrier] using hLam
  rcases recarrierLamInferInv body tIn id Sum.inl id (.fn compileIn compileOut)
    hLamCore with ⟨bodyFuel, bodyType, hBody, hType⟩
  have hInputType := (AST.fn.inj hType).1
  have hOutputType := (AST.fn.inj hType).2
  subst compileIn
  subst compileOut
  let inputType : AST.Typ build.BuildParameters := tIn.recarrier id Sum.inl id
  let index := build.uid2typCtx.inv inputType
  let receipt := exe.uid2valCtx.inv input
  let leftBodyB : refs.ExeParameters.B ⊕ Unit →
      build.BuildParameters.F ⊕ build.BuildParameters.B :=
    λ bound =>
      match bound with
      | .inl outer => .inl outer
      | .inr () => .inr index
  let rightBodyB : refs.ExeParameters.B ⊕ Unit →
      build.BuildParameters.F ⊕ build.BuildParameters.B :=
    λ bound =>
      match bound with
      | .inl outer => .inl outer
      | .inr () => .inl receipt
  have hFree :
      ∀ (free : refs.ExeParameters.F) (typ : AST.Typ build.BuildParameters),
        (∃ inferFuel,
          (AST.ref (.inl free) : AST.Trm build.BuildParameters).inferCore inferFuel =
            .yield (some typ)) →
        ∃ inferFuel,
          (AST.ref (.inl free) : AST.Trm build.BuildParameters).inferCore inferFuel =
            .yield (some typ) := by
    intro free typ hRef
    exact hRef
  have hBound :
      ∀ (bound : refs.ExeParameters.B ⊕ Unit)
        (typ : AST.Typ build.BuildParameters),
        (∃ inferFuel,
          (AST.ref (leftBodyB bound) : AST.Trm build.BuildParameters).inferCore
            inferFuel = .yield (some typ)) →
        ∃ inferFuel,
          (AST.ref (rightBodyB bound) : AST.Trm build.BuildParameters).inferCore
            inferFuel = .yield (some typ) := by
    intro bound typ hRef
    cases bound with
    | inl outer => exact hRef
    | inr newest =>
      cases newest
      rcases hRef with ⟨inferFuel, hRef⟩
      cases inferFuel with
      | zero => simp [AST.inferCore] at hRef
      | succ inferFuel =>
        have hRefType : inputType = typ := by
          simpa [AST.inferCore, leftBodyB, index] using hRef
        subst typ
        rcases hInput with ⟨inputFuel, hInput⟩
        exact ⟨inputFuel + 1, by
          simpa [AST.inferCore, AST.infer, rightBodyB, receipt] using hInput⟩
  have hLeftBody : ∃ inferFuel,
      (body.recarrier (Q := build.BuildParameters) id leftBodyB id).inferCore inferFuel =
        .yield (some bodyType) := by
    refine ⟨bodyFuel, ?_⟩
    rw [← hBody]
    apply congrArg (λ term : AST.Trm build.BuildParameters => term.inferCore bodyFuel)
    apply recarrierCongr
    · intro free
      rfl
    · intro bound
      cases bound with
      | inl outer => rfl
      | inr newest => cases newest; rfl
    · intro repr
      rfl
  have hRightBody := recarrierTrmInfer body id id leftBodyB rightBodyB id id
    hFree hBound bodyType hLeftBody
  rcases hRightBody with ⟨rightFuel, hRightBody⟩
  have hBetaBuild :
      (body.instantiateLamBody receipt).exe2build =
        body.recarrier (Q := build.BuildParameters) id rightBodyB id := by
    simp only [AST.instantiateLamBody, AST.exe2build, recarrierComp, id_eq]
    apply recarrierCongr
    · intro free
      rfl
    · intro bound
      cases bound with
      | inl outer => rfl
      | inr newest => cases newest; rfl
    · intro repr
      rfl
  refine ⟨rightFuel, ?_⟩
  simp only [AST.infer]
  rw [hBetaBuild]
  simpa only [rightBodyB] using hRightBody

/-- Successful inference is preserved by every finite evaluation observation. -/
private theorem inferEval {refs : ExeRefs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (evalFuel : Nat) (trm : AST.Trm refs.ExeParameters)
    (typ : AST.Typ build.BuildParameters)
    (hInfer : ∃ inferFuel, trm.infer inferFuel = .yield (some typ)) :
    match trm.eval evalFuel with
    | .outOfFuel => True
    | .yield none => False
    | .yield (some value) =>
      ∃ inferFuel, value.asTrm.infer inferFuel = .yield (some typ) := by
  induction evalFuel generalizing trm typ with
  | zero => simp [AST.eval]
  | succ evalFuel ih =>
    cases trm with
    | val value => simpa [AST.eval, AST.Val.asTrm] using hInfer
    | ref source =>
      cases source with
      | inl receipt =>
        have hStored := referenceInferInv receipt typ hInfer
        simpa [AST.eval] using hStored
      | inr receipt =>
        have hFree : ∃ inferFuel,
            (AST.ref (.inl receipt) : AST.Trm refs.ExeParameters).infer inferFuel =
              .yield (some typ) := by
          simpa [AST.infer, AST.exe2build, AST.recarrier] using hInfer
        have hStored := referenceInferInv receipt typ hFree
        simpa [AST.eval] using hStored
    | apply fnTerm arg =>
      rcases applyInferInv fnTerm arg typ hInfer with
        ⟨inferFuel, tIn, tOut, hFn, hArg, hType⟩
      subst typ
      cases hFnEval : fnTerm.eval evalFuel with
      | outOfFuel => simp [AST.eval, hFnEval]
      | yield fnResult =>
        have hFnResult := ih fnTerm (.fn tIn tOut) ⟨inferFuel, hFn⟩
        simp only [hFnEval] at hFnResult
        cases hArgEval : arg.eval evalFuel with
        | outOfFuel => simp [AST.eval, hFnEval, hArgEval]
        | yield argResult =>
          have hArgResult := ih arg tIn ⟨inferFuel, hArg⟩
          simp only [hArgEval] at hArgResult
          cases fnResult with
          | none => exact False.elim hFnResult
          | some fnValue =>
            cases fnValue with
            | lit repr => exact False.elim (literalNotFunction repr tIn tOut hFnResult)
            | lam body sourceIn =>
              cases argResult with
              | none => exact False.elim hArgResult
              | some input =>
                have hBeta := betaInfer body sourceIn input tIn tOut
                  hFnResult hArgResult
                have hBodyResult := ih
                  (body.instantiateLamBody (exe.uid2valCtx.inv input)) tOut hBeta
                simpa only [AST.eval, hFnEval, hArgEval] using hBodyResult

/-- A successfully inferred executable term satisfies the public safety judgment. -/
private theorem inferredSafety {refs : ExeRefs} [build : BuildEnv refs]
    (trm : AST.Trm refs.ExeParameters) (typ : AST.Typ build.BuildParameters)
    (hInfer : ∃ inferFuel, trm.infer inferFuel = .yield (some typ)) :
    [_exe : ExeEnv refs] → Safety trm typ := by
  intro _exe
  unfold Safety RecOpt.isSemiDecidable
  intro evalFuel
  have hPreserved := inferEval evalFuel trm typ hInfer
  cases hEval : trm.eval evalFuel with
  | outOfFuel => trivial
  | yield result =>
    cases result with
    | none =>
      simp only [hEval] at hPreserved
    | some value =>
      simp only [hEval] at hPreserved
      unfold RecOpt.isDecidable
      rcases hPreserved with ⟨inferFuel, hValue⟩
      refine ⟨inferFuel, ?_⟩
      rw [hValue]
      rfl

/-
This is an agumented version of [AST.Trm.infer].

There is only 1 difference: it must produce a type judge with safety proof that trm always evaluate to a value of the same type

It also has access to [ProvingEnv], a mirror of [BuildEnv] with [uid2typWithSafetyCtx] : an extra equivalence between type with safety proof and a subtype of UId

TODO: discharge this function.
- The execution of `Trm.infer` should yield identical `TypeWithSafey.t2` without safety proof
- If the original `Trm.infer` is unsafe, revise it to be safe first
- You are allowed to add more context into ProvingEnv namespace to meet proving demand
-/
/-- Infers build types for executable terms. -/
def infer [refs : ExeRefs] [proving : ProvingEnv refs] [env : ExeEnv refs]
    (trm : ∀ {B : UIdU}, AST.Trm { F := refs.uid2val.UId, B := B, D := refs.D }) :
    RecOpt (TypeWithSafey trm)
  | fuel =>
    match hInfer : (@trm refs.uid2val.UId).infer fuel with
    | .outOfFuel => .outOfFuel
    | .yield none => .yield none
    | .yield (some typ) =>
      .yield (some {
        t2 := typ
        safety := inferredSafety (@trm refs.uid2val.UId) typ ⟨fuel, hInfer⟩
      })

end Umbral

end Lp2lc.Active.STLC
