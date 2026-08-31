import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.__Infer
import «Lp2lc».Active.STLC.__Proof_unused

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec
open AST
open Parameters

namespace AST

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone [refs : ExeRefs] [env : BuildEnv refs]
    (trm : Trm env.BuildParameters) : -- TODO: lift this core theorem to `infer`
    trm.inferCore.Monotone := by
  intro less more result hFuel hInfer
  induction less using Nat.strongRecOn generalizing trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [inferCore] at hInfer
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel ≤ toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          cases value with
          | lit repr => simpa [inferCore] using hInfer
          | lam body tIn =>
            simp only [inferCore, Outcome.map] at hInfer ⊢
            split at hInfer
            next _ bodyResult hBody =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                _ toFuel bodyResult hFuelTail hBody
              simpa only [hBodyTop] using hInfer
            next _ hBody =>
              cases hInfer
        | apply fnTerm arg =>
          cases hFn : fnTerm.inferCore fuel with
          | outOfFuel => simp [inferCore, hFn] at hInfer
          | yield fnResult =>
            cases hArg : arg.inferCore fuel with
            | outOfFuel => simp [inferCore, hFn, hArg] at hInfer
            | yield argResult =>
              have hFnTop := ih fuel (Nat.lt_succ_self fuel)
                fnTerm toFuel fnResult hFuelTail hFn
              have hArgTop := ih fuel (Nat.lt_succ_self fuel)
                arg toFuel argResult hFuelTail hArg
              simpa [inferCore, hFn, hArg, hFnTop, hArgTop] using hInfer
        | ref receipt =>
          cases receipt with
          | inl rc =>
            let executable : Trm refs.ExeParameters := (refs.uid2val.get rc).asTrm
            let original := executable.exe2build
            have hOriginal : original.inferCore fuel = .yield result := by
              simpa [inferCore, executable, original] using hInfer
            have hOriginalTop := ih fuel (Nat.lt_succ_self fuel)
              original toFuel result hFuelTail hOriginal
            simpa [inferCore, executable, original] using hOriginalTop
          | inr rc =>
            cases env.uid2typ.get rc with
            | primitive => simpa [inferCore] using hInfer
            | fn tIn tOut => simpa [inferCore] using hInfer

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone [refs : ExeRefs] [env : BuildEnv refs]
    (value : Val env.BuildParameters) :
    value.asTrm.inferCore.Monotone :=
  termInferMonotone value.asTrm

end AST

/-- Type syntax is independent of every free, bound, and data carrier map. -/
private theorem recarrierTypEq {refs : ExeRefs} [build : BuildEnv refs]
    {P : Parameters} (self : AST.Typ P)
    (left right : CarrierMap P build.BuildParameters) :
    self.recarrier left = self.recarrier right :=
  match self with
  | .primitive => rfl
  | .fn tIn tOut => by
    simp only [AST.recarrier]
    rw [recarrierTypEq tIn left right, recarrierTypEq tOut left right]

/-- Recarriering a body before introducing a fresh target binder commutes with specialization. -/
private theorem recarrierSpecialise {P Q : Parameters} (self : LamBody P)
    (map : CarrierMap P Q) (arg : Q.F ⊕ Q.B) :
    (self.recarrier map).specialise (CarrierMap.identity _) arg =
      self.specialise map arg := by
  cases self with
  | mk body =>
    simp only [LamBody.specialise, LamBody.body, LamBody.recarrier,
      AST.recarrierComposability]
    apply congrArg body.recarrier
    ext value
    · rfl
    · cases value with
      | inl outer =>
        cases h : map.mapB outer <;> simp [CarrierMap.«then», CarrierMap.identity,
          CarrierMap.bind, CarrierMap.mapRef, CarrierMap.underBinder, h]
      | inr newest => cases newest; rfl
    · rfl

/-- A mapped successful outcome exposes the successful source outcome. -/
private theorem outcomeMapYield {T T2 : Type 2} (self : Rec.Outcome T)
    (map : T → T2) (result : T2) (hResult : self.map map = .yield result) :
    ∃ source, self = .yield source ∧ map source = result := by
  cases self with
  | outOfFuel => cases hResult
  | yield source => exact ⟨source, rfl, Rec.Outcome.yield.inj hResult⟩

/-- Successful lambda inference exposes successful inference of its instantiated body. -/
private theorem lamInferInv {refs : ExeRefs} [build : BuildEnv refs]
    (body : LamBody build.BuildParameters)
    (tIn typ : AST.Typ build.BuildParameters)
    (hInfer : ∃ fuel, (AST.val (.lam body tIn) : AST.Trm build.BuildParameters).inferCore
      fuel = .yield (some typ)) :
    ∃ fuel tOut,
      (body.specialise (CarrierMap.identity _)
        (.inr (build.uid2typCtx.inv tIn))).inferCore fuel =
        .yield (some tOut) ∧
      typ = .fn tIn tOut := by
  rcases hInfer with ⟨fuel, hInfer⟩
  cases fuel with
  | zero => simp [AST.inferCore] at hInfer
  | succ fuel =>
    simp only [AST.inferCore] at hInfer
    have hMapped := outcomeMapYield
      ((body.specialise (CarrierMap.identity _)
        (.inr (build.uid2typCtx.inv tIn))).inferCore fuel)
      (λ out => out.map (λ tOut => AST.fn tIn tOut)) (some typ) hInfer
    rcases hMapped with ⟨bodyResult, hBody, hType⟩
    cases bodyResult with
    | none => cases hType
    | some tOut => exact ⟨fuel, tOut, hBody, (Option.some.inj hType).symm⟩

/-- Successful instantiated-body inference reconstructs successful lambda inference. -/
private theorem lamInferIntro {refs : ExeRefs} [build : BuildEnv refs]
    (body : LamBody build.BuildParameters)
    (tIn tOut : AST.Typ build.BuildParameters) (fuel : Nat)
    (hBody : (body.specialise (CarrierMap.identity _)
      (.inr (build.uid2typCtx.inv tIn))).inferCore fuel =
      .yield (some tOut)) :
    (AST.val (.lam body tIn) : AST.Trm build.BuildParameters).inferCore (fuel + 1) =
      .yield (some (.fn tIn tOut)) := by
  have hMapped := congrArg
    (λ result => result.map (λ out => out.map (λ bodyType => AST.fn tIn bodyType)))
    hBody
  simpa only [AST.inferCore, Rec.Outcome.map, Option.map] using hMapped

/-- Recarried lambda inference exposes the normalized compiler body. -/
private theorem recarrierLamInferInv {refs : ExeRefs} [build : BuildEnv refs]
    {P : Parameters}
    (body : LamBody P) (tIn : AST.Typ P)
    (map : CarrierMap P build.BuildParameters)
    (typ : AST.Typ build.BuildParameters)
    (hInfer : ∃ fuel,
      (AST.val ((AST.lam body tIn).recarrier map) :
        AST.Trm build.BuildParameters).inferCore fuel = .yield (some typ)) :
    ∃ fuel tOut,
      (body.specialise map (.inr (build.uid2typCtx.inv
        (tIn.recarrier map)))).inferCore fuel = .yield (some tOut) ∧
      typ = .fn (tIn.recarrier map) tOut := by
  have hCarried : ∃ fuel,
      (AST.val (.lam (body.recarrier map) (tIn.recarrier map)) :
        AST.Trm build.BuildParameters).inferCore fuel = .yield (some typ) := by
    simpa only [AST.recarrier] using hInfer
  rcases lamInferInv (build := build) (body.recarrier map) (tIn.recarrier map)
    typ hCarried with ⟨fuel, tOut, hBody, hType⟩
  rw [recarrierSpecialise] at hBody
  exact ⟨fuel, tOut, hBody, hType⟩

/-- Normalized compiler-body inference reconstructs recarried lambda inference. -/
private theorem recarrierLamInferIntro {refs : ExeRefs} [build : BuildEnv refs]
    {P : Parameters}
    (body : LamBody P) (tIn : AST.Typ P)
    (map : CarrierMap P build.BuildParameters)
    (tOut : AST.Typ build.BuildParameters)
    (fuel : Nat)
    (hBody : (body.specialise map (.inr (build.uid2typCtx.inv
      (tIn.recarrier map)))).inferCore fuel = .yield (some tOut)) :
    (AST.val ((AST.lam body tIn).recarrier map) :
      AST.Trm build.BuildParameters).inferCore (fuel + 1) =
        .yield (some (.fn (tIn.recarrier map) tOut)) := by
  have hInstantiated :
      ((body.recarrier map).specialise (CarrierMap.identity _)
        (.inr (build.uid2typCtx.inv (tIn.recarrier map)))).inferCore fuel =
          .yield (some tOut) := by
    rw [recarrierSpecialise]
    exact hBody
  simpa only [AST.recarrier] using lamInferIntro (build := build)
    (body.recarrier map) (tIn.recarrier map) tOut fuel hInstantiated

mutual

  /-- Counts syntax constructors to justify semantic recursion through a lambda body. -/
  private def syntaxSize {P : Parameters} {l : Label} (self : AST P l) : Nat :=
    match self with
    | .primitive => 1
    | .fn tIn tOut => syntaxSize tIn + syntaxSize tOut + 1
    | .val value => syntaxSize value + 1
    | .apply fnTerm arg => syntaxSize fnTerm + syntaxSize arg + 1
    | .ref _ => 1
    | .lit _ => 1
    | .lam body tIn => lamBodySyntaxSize body + syntaxSize tIn + 1

  /-- Counts the wrapper constructor together with its stored body syntax. -/
  private def lamBodySyntaxSize {P : Parameters} (self : LamBody P) : Nat :=
    match self with
    | .mk body => syntaxSize body + 1

end

@[simp]
private theorem lamBodySyntaxSizeEq {P : Parameters} (self : LamBody P) :
    lamBodySyntaxSize self = syntaxSize self.body + 1 := by
  cases self
  rfl

mutual

  private theorem recarrierValInfer {refs : ExeRefs} [build : BuildEnv refs]
      {P : Parameters} (self : AST.Val P)
      (left right : CarrierMap P build.BuildParameters)
      (hFree : ∀ (free : P.F) (typ : AST.Typ build.BuildParameters),
        (∃ fuel, (AST.ref (.inl (left.mapF free)) :
          AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ)) →
        ∃ fuel, (AST.ref (.inl (right.mapF free)) :
          AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ))
      (hBound : ∀ (bound : P.B) (typ : AST.Typ build.BuildParameters),
        (∃ fuel, (AST.ref (left.mapB bound) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ)) →
        ∃ fuel, (AST.ref (right.mapB bound) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ))
      (typ : AST.Typ build.BuildParameters)
      (hInfer : ∃ fuel,
        (AST.val (self.recarrier left)).inferCore fuel = .yield (some typ)) :
      ∃ fuel, (AST.val (self.recarrier right)).inferCore fuel =
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
      rcases recarrierLamInferInv body tIn left typ hInfer with
        ⟨fuel, bodyType, hBody, hType⟩
      subst typ
      let leftBodyMap := left.bind (.inr (build.uid2typCtx.inv (tIn.recarrier left)))
      have hInputType := recarrierTypEq tIn left right
      let rightBodyMap := right.bind (.inr (build.uid2typCtx.inv (tIn.recarrier right)))
      have hIndex :
          build.uid2typCtx.inv (tIn.recarrier left) =
            build.uid2typCtx.inv (tIn.recarrier right) :=
        congrArg build.uid2typCtx.inv hInputType
      have hNestedBound :
          ∀ (bound : P.B ⊕ Unit) (refType : AST.Typ build.BuildParameters),
            (∃ refFuel,
              (AST.ref (leftBodyMap.mapB bound) : AST.Trm build.BuildParameters).inferCore
                refFuel = .yield (some refType)) →
            ∃ refFuel,
              (AST.ref (rightBodyMap.mapB bound) : AST.Trm build.BuildParameters).inferCore
                refFuel = .yield (some refType) := by
        intro bound refType hRef
        cases bound with
        | inl outer =>
          have hOuter := hBound outer refType hRef
          simpa only [leftBodyMap, rightBodyMap, CarrierMap.bind] using hOuter
        | inr newest =>
          cases newest
          simpa only [leftBodyMap, rightBodyMap, CarrierMap.bind, hIndex] using hRef
      have hRightBody := recarrierTrmInfer body.body leftBodyMap rightBodyMap
        hFree hNestedBound bodyType ⟨fuel, hBody⟩
      rcases hRightBody with ⟨rightFuel, hRightBody⟩
      refine ⟨rightFuel + 1, ?_⟩
      rw [hInputType]
      simpa only [LamBody.specialise, rightBodyMap] using
        recarrierLamInferIntro body tIn right bodyType rightFuel hRightBody
  termination_by syntaxSize self
  decreasing_by
    all_goals
      first
      | cases ‹self ≍ AST.lam _ _›
      | cases ‹self ≍ AST.val _›
      | cases ‹self ≍ AST.apply _ _›
      simp [syntaxSize, lamBodySyntaxSizeEq, LamBody.body] <;> omega

  private theorem recarrierTrmInfer {refs : ExeRefs} [build : BuildEnv refs]
      {P : Parameters} (self : AST.Trm P)
      (left right : CarrierMap P build.BuildParameters)
      (hFree : ∀ (free : P.F) (typ : AST.Typ build.BuildParameters),
        (∃ fuel, (AST.ref (.inl (left.mapF free)) :
          AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ)) →
        ∃ fuel, (AST.ref (.inl (right.mapF free)) :
          AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ))
      (hBound : ∀ (bound : P.B) (typ : AST.Typ build.BuildParameters),
        (∃ fuel, (AST.ref (left.mapB bound) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ)) →
        ∃ fuel, (AST.ref (right.mapB bound) : AST.Trm build.BuildParameters).inferCore fuel =
          .yield (some typ))
      (typ : AST.Typ build.BuildParameters)
      (hInfer : ∃ fuel,
        (self.recarrier left).inferCore fuel = .yield (some typ)) :
      ∃ fuel, (self.recarrier right).inferCore fuel = .yield (some typ) := by
    cases self with
    | val value =>
      exact recarrierValInfer value left right hFree hBound typ hInfer
    | ref source =>
      cases source with
      | inl free => exact hFree free typ hInfer
      | inr bound => exact hBound bound typ hInfer
    | apply fnTerm arg =>
      rcases hInfer with ⟨fuel, hInfer⟩
      cases fuel with
      | zero => simp [AST.inferCore] at hInfer
      | succ fuel =>
        let leftFn := fnTerm.recarrier left
        let rightFn := fnTerm.recarrier right
        let leftArg := arg.recarrier left
        let rightArg := arg.recarrier right
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
                    have hRightFn := recarrierTrmInfer fnTerm left right
                      hFree hBound (.fn tIn tOut) ⟨fuel, hFn⟩
                    have hRightArg := recarrierTrmInfer arg left right
                      hFree hBound argType ⟨fuel, hArg⟩
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
  termination_by syntaxSize self
  decreasing_by
    all_goals
      first
      | cases ‹self ≍ AST.lam _ _›
      | cases ‹self ≍ AST.val _›
      | cases ‹self ≍ AST.apply _ _›
      simp [syntaxSize] <;> omega

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
      simpa [AST.infer, AST.exe2build, AST.inferCore,
        CarrierMap.mapRef] using hInfer⟩

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

/-- A successful value-inference observation at an equal type exposes its exact equation. -/
private theorem valueInferExact {refs : ExeRefs} [build : BuildEnv refs]
    (value : AST.Val refs.ExeParameters) (typ : AST.Typ build.BuildParameters)
    (hInfer : value.asTrm.infer.isDecidable (λ inferred => inferred ≤ typ)) :
    ∃ inferFuel, value.asTrm.infer inferFuel = .yield (some typ) := by
  unfold RecOpt.isDecidable at hInfer
  rcases hInfer with ⟨inferFuel, hInfer⟩
  cases hResult : value.asTrm.infer inferFuel with
  | outOfFuel => simp [hResult] at hInfer
  | yield result =>
    cases result with
    | none => simp [hResult] at hInfer
    | some inferred =>
      simp only [hResult] at hInfer
      change inferred = typ at hInfer
      subst typ
      exact ⟨inferFuel, hResult⟩

/-- Structural lambda inference is preserved when the compiler slot is beta-instantiated. -/
private theorem betaInfer {refs : ExeRefs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (body : LamBody refs.ExeParameters)
    (tIn : AST.Typ refs.ExeParameters) (input : AST.Val refs.ExeParameters)
    (compileIn compileOut : AST.Typ build.BuildParameters)
    (hLam : ∃ inferFuel,
      (AST.val (.lam body tIn) : AST.Trm refs.ExeParameters).infer inferFuel =
        .yield (some (.fn compileIn compileOut)))
    (hInput : ∃ inferFuel, input.asTrm.infer inferFuel =
      .yield (some compileIn)) :
    ∃ inferFuel,
      (body.specialise (CarrierMap.identity _)
        (.inr (exe.uid2valCtx.inv input))).infer inferFuel =
        .yield (some compileOut) := by
  let exeToBuild : CarrierMap refs.ExeParameters build.BuildParameters :=
    { mapF := id, mapB := Sum.inl, mapD := id }
  have hLamCore : ∃ inferFuel,
      (AST.val ((AST.lam body tIn).recarrier exeToBuild) :
        AST.Trm build.BuildParameters).inferCore inferFuel =
          .yield (some (.fn compileIn compileOut)) := by
    simpa only [AST.infer, AST.exe2build, AST.recarrier, exeToBuild] using hLam
  rcases recarrierLamInferInv body tIn exeToBuild (.fn compileIn compileOut)
    hLamCore with ⟨bodyFuel, bodyType, hBody, hType⟩
  have hInputType := (AST.fn.inj hType).1
  have hOutputType := (AST.fn.inj hType).2
  subst compileIn
  subst compileOut
  let inputType : AST.Typ build.BuildParameters := tIn.recarrier exeToBuild
  let index := build.uid2typCtx.inv inputType
  let receipt := exe.uid2valCtx.inv input
  let leftBodyMap := exeToBuild.bind (.inr index)
  let rightBodyMap := exeToBuild.bind (.inl receipt)
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
          (AST.ref (leftBodyMap.mapB bound) : AST.Trm build.BuildParameters).inferCore
            inferFuel = .yield (some typ)) →
        ∃ inferFuel,
          (AST.ref (rightBodyMap.mapB bound) : AST.Trm build.BuildParameters).inferCore
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
          simpa [AST.inferCore, leftBodyMap, exeToBuild, CarrierMap.bind,
            index] using hRef
        subst typ
        rcases hInput with ⟨inputFuel, hInput⟩
        exact ⟨inputFuel + 1, by
          simpa [AST.inferCore, AST.infer, rightBodyMap, exeToBuild,
            CarrierMap.bind, receipt, CarrierMap.mapRef] using hInput⟩
  have hLeftBody : ∃ inferFuel,
      (body.body.recarrier leftBodyMap).inferCore inferFuel =
        .yield (some bodyType) := by
    exact ⟨bodyFuel, by simpa only [LamBody.specialise, leftBodyMap,
      inputType, index] using hBody⟩
  have hRightBody := recarrierTrmInfer body.body leftBodyMap rightBodyMap
    hFree hBound bodyType hLeftBody
  rcases hRightBody with ⟨rightFuel, hRightBody⟩
  have hSpecialisedRight :
      (body.specialise exeToBuild (.inl receipt)).inferCore rightFuel =
        .yield (some bodyType) := by
    simpa only [LamBody.specialise, rightBodyMap] using hRightBody
  have hBetaBuild :
      (body.specialise (CarrierMap.identity _) (.inr receipt)).exe2build =
        body.specialise exeToBuild (.inl receipt) := by
    simpa only [AST.exe2build, exeToBuild, CarrierMap.identityThen,
      CarrierMap.mapRef] using
        body.specialiseNaturality (CarrierMap.identity _) exeToBuild (.inr receipt)
  refine ⟨rightFuel, ?_⟩
  simp only [AST.infer]
  rw [hBetaBuild]
  exact hSpecialisedRight

/-
TODO: Prove `fundamental` as the canonical pointwise soundness lemma for `AST.Trm.infer`
without changing its statement. Use `hInfer` to eliminate explicit failure and
out-of-fuel branches and to expose successful recursive-inference equations. After
this proof is complete, discharge `fundamental_fwd` from `fundamental` by
unfolding `RecOpt.ifSucceedMustSatisfy` and splitting on `trm.infer fuel`; do not
maintain two independent soundness proofs.
-/
/-- A successfully inferred type makes the executable term safe at that type. -/
theorem fundamental {refs : ExeRefs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm refs.ExeParameters) (fuel : Nat)
    (typ : AST.Typ build.BuildParameters)
    (hInfer : trm.infer fuel = .yield (some typ)) :
    Safety trm typ := by
  unfold Safety RecOpt.isSemiDecidable
  intro evalFuel
  induction evalFuel generalizing trm fuel typ with
  | zero => simp [AST.eval]
  | succ evalFuel ih =>
    cases trm with
    | val value =>
      change (AST.Val.asTrm value).infer.isDecidable (λ inferred => inferred ≤ typ)
      change (AST.Val.asTrm value).infer fuel = .yield (some typ) at hInfer
      unfold RecOpt.isDecidable
      exact ⟨fuel, by rw [hInfer]; rfl⟩
    | ref source =>
      cases source with
      | inl receipt =>
        have hStored := referenceInferInv receipt typ ⟨fuel, hInfer⟩
        rcases hStored with ⟨storedFuel, hStored⟩
        change (refs.uid2val.get receipt).asTrm.infer.isDecidable
          (λ inferred => inferred ≤ typ)
        unfold RecOpt.isDecidable
        exact ⟨storedFuel, by rw [hStored]; rfl⟩
      | inr receipt =>
        have hFree : ∃ inferFuel,
            (AST.ref (.inl receipt) : AST.Trm refs.ExeParameters).infer inferFuel =
              .yield (some typ) := by
          exact ⟨fuel, by simpa [AST.infer, AST.exe2build, AST.recarrier,
            CarrierMap.mapRef] using hInfer⟩
        have hStored := referenceInferInv receipt typ hFree
        rcases hStored with ⟨storedFuel, hStored⟩
        change (refs.uid2val.get receipt).asTrm.infer.isDecidable
          (λ inferred => inferred ≤ typ)
        unfold RecOpt.isDecidable
        exact ⟨storedFuel, by rw [hStored]; rfl⟩
    | apply fnTerm arg =>
      rcases applyInferInv fnTerm arg typ ⟨fuel, hInfer⟩ with
        ⟨inferFuel, tIn, tOut, hFn, hArg, hType⟩
      subst typ
      cases hFnEval : fnTerm.eval evalFuel with
      | outOfFuel => simp [AST.eval, hFnEval]
      | yield fnResult =>
        have hFnSafe := ih fnTerm inferFuel (.fn tIn tOut) hFn
        simp only [hFnEval] at hFnSafe
        cases hArgEval : arg.eval evalFuel with
        | outOfFuel => simp [AST.eval, hFnEval, hArgEval]
        | yield argResult =>
          have hArgSafe := ih arg inferFuel tIn hArg
          simp only [hArgEval] at hArgSafe
          cases fnResult with
          | none => simp at hFnSafe
          | some fnValue =>
            cases fnValue with
            | lit repr =>
              have hFnExact := valueInferExact (.lit repr) (.fn tIn tOut) hFnSafe
              exact False.elim (literalNotFunction repr tIn tOut hFnExact)
            | lam body sourceIn =>
              cases argResult with
              | none => simp at hArgSafe
              | some input =>
                have hFnExact := valueInferExact (.lam body sourceIn) (.fn tIn tOut) hFnSafe
                have hInputExact := valueInferExact input tIn hArgSafe
                rcases betaInfer body sourceIn input tIn tOut hFnExact hInputExact with
                  ⟨bodyFuel, hBody⟩
                have hBodySafe := ih
                  (body.specialise (CarrierMap.identity _)
                    (.inr (exe.uid2valCtx.inv input))) bodyFuel tOut hBody
                simpa only [AST.eval, hFnEval, hArgEval] using hBodySafe

/--
alternative formulation of fundamental lemma that has fewer argument, but proof is less straightforward (because lean metaprogramming)
-/
theorem fundamental_fwd {refs : ExeRefs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm refs.ExeParameters) : trm.infer.ifSucceedMustSatisfy (
    λ t1 =>
      Safety trm t1
  ) := by
  unfold RecOpt.ifSucceedMustSatisfy
  intro fuel
  cases hInfer : trm.infer fuel with
  | outOfFuel => rfl
  | yield result =>
    cases result with
    | none => rfl
    | some typ => exact fundamental trm fuel typ hInfer

/-
TODO: the above are "Paranoid Fundamental Lemma": compilation may fail even but term evaluation may succeed, can this be improved?
-/

end STLC
