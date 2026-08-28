import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Parameters
open AST

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
    simp only [LamBody.specialise, LamBody.body, LamBody.recarrier, AST.recarrierComp]
    apply congrArg body.recarrier
    ext value
    · rfl
    · cases value with
      | inl outer => cases h : map.mapB outer <;> simp [CarrierMap.«then»,
          CarrierMap.identity, CarrierMap.bind, CarrierMap.mapRef,
          CarrierMap.underBinder, h]
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
        hFree hNestedBound bodyType
        ⟨fuel, hBody⟩
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
          simpa [AST.infer, AST.exe2build, AST.recarrier,
            CarrierMap.mapRef] using hInfer
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
                  (body.specialise (CarrierMap.identity _)
                    (.inr (exe.uid2valCtx.inv input))) tOut hBeta
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
