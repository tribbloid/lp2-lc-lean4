import «Lp2lc».Active.STLC.UId.__Infer

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util EnvBase EnvBase.Trm

/-- A runtime source context, including the free references in its stored function bodies.

Its shared lookups must contain values whose canonical syntax agrees with the transported source
value. This excludes type-only references throughout captured values without assuming their safety.
-/
structure RuntimeContext (refs : UIdRefs) where
  base : EnvBase
  values : KVRefs base.UId base.Val
  embed : base.UId → refs.UId
  compatible : ∀ receipt, (refs.uid2both.get (embed receipt)).elim
    (λ value => Val.Same value (AST.recarrier (values.get receipt) (.mk embed))) (λ _ => False)

section variable {refs : UIdRefs} [build : BuildEnv refs] [exe : ExeEnv refs]

/-- Every completed evaluation succeeds, and its value can be inferred at the claimed type. -/
def Safety (trm : refs.base.Trm) (typ : refs.base.Typ) : Prop :=
  trm.eval.isSemiDecidable
    (λ value => value.asTrm.infer.isDecidable (λ inferred => inferred ≤ typ))

end

private theorem mapRefComp {source P Q R : Parameters}
    (under : source.Under P) (first : CarrierMap P Q) (second : CarrierMap Q R)
    (carrier : source.TRef) :
    match first, second with
    | .mk first, .mk second =>
      mapRef under (.mk (second ∘ first)) carrier = second (mapRef under (.mk first) carrier) := by
  induction under generalizing Q R with
  | same => cases first; cases second; rfl
  | @lower p2 prev ih =>
    rcases p2 with ⟨⟨byteCode⟩, encoding, index⟩
    cases first with
    | mk first =>
      cases second with
      | mk second => exact ih (.mk (λ carrier => first (.inl carrier))) (.mk second)

/-- Transport composes while opening every binder only at its canonical slot. -/
private theorem recarrierComp {P Q R l} (self : Pre.AST P l)
    (first : CarrierMap P Q) (second : CarrierMap Q R) :
    match first, second with
    | .mk first, .mk second =>
      AST.recarrier (AST.recarrier self (.mk first)) (.mk second) =
        AST.recarrier self (.mk (second ∘ first)) := by
  induction self using Pre.AST.rec
    (motive_1 := λ P l self => ∀ {Q R} (first : CarrierMap P Q) (second : CarrierMap Q R),
      match first, second with
      | .mk first, .mk second =>
        Binder.recarrier (Binder.recarrier self (.mk first)) (.mk second) =
          Binder.recarrier self (.mk (second ∘ first))) generalizing Q R with
  | mk body ih =>
    rename_i Q R first second
    cases first with
    | @mk B C D first => cases second with
      | @mk _ _ E second =>
        change Pre.Binder.mk (P := {B := B, I := IndexEncoding.FreeOrUnit, index := E})
          (λ _ => AST.recarrier (AST.recarrier (body (.inr ()))
            (.mk (Sum.map first (id : Unit → Unit)))) (.mk (Sum.map second id))) =
          Pre.Binder.mk (λ _ => AST.recarrier (body (.inr ())) (.mk (Sum.map (second ∘ first) id)))
        apply congrArg Pre.Binder.mk
        funext carrier
        rw [ih (.inr ()) (.mk (Sum.map first id)) (.mk (Sum.map second id))]
        congr 2
        funext carrier
        cases carrier <;> rfl
  | TLit => cases first; cases second; rfl
  | lit repr => cases first; cases second; rfl
  | TFn tIn tOut ihIn ihOut =>
    cases first; cases second
    rename_i _ _ _ first _ second
    simp only [AST.recarrier]
    rw [ihIn (.mk first) (.mk second), ihOut (.mk first) (.mk second)]
  | fn tIn body ihIn ihBody =>
    cases first; cases second
    rename_i _ _ _ first _ second
    simp only [AST.recarrier]
    rw [ihIn (.mk first) (.mk second), ihBody (.mk first) (.mk second)]
  | val value ih =>
    cases first; cases second
    rename_i _ _ _ first _ second
    exact congrArg Pre.AST.val (ih (.mk first) (.mk second))
  | apply fn arg ihFn ihArg =>
    cases first; cases second
    rename_i _ _ _ first _ second
    simp only [AST.recarrier]
    rw [ihFn (.mk first) (.mk second), ihArg (.mk first) (.mk second)]
  | ref carrier under =>
    cases first with
    | mk first => cases second with
      | mk second =>
        exact congrArg (λ carrier => Pre.AST.ref carrier .same)
          (mapRefComp under (.mk first) (.mk second) carrier).symm

private theorem typRecarrier {source target : EnvBase} (typ : source.Typ)
    (first second : source.UId → target.UId) :
    AST.recarrier typ (.mk first) = AST.recarrier typ (.mk second) := by
  cases typ with
  | TLit => rfl
  | TFn input output =>
    simp only [AST.recarrier]
    rw [typRecarrier input first second, typRecarrier output first second]
termination_by sizeOf typ

private theorem applyRecarrier {source target : EnvBase} (body : source.Binder .trm)
    (map : source.UId → target.UId) (receipt : target.UId) :
    Binder.apply (Binder.recarrier body (.mk map)) receipt =
      AST.recarrier (Pre.Binder.apply body (.inr ())) (.mk (Sum.elim map (λ _ => receipt))) := by
  cases body with
  | mk body =>
    change AST.recarrier (AST.recarrier (body (.inr ())) (.mk (Sum.map map id)))
      (.mk (Sum.elim id (λ _ => receipt))) = _
    rw [recarrierComp (body (.inr ())) (.mk (Sum.map map id)) (.mk (Sum.elim id (λ _ => receipt)))]
    congr 2
    funext carrier
    cases carrier <;> rfl

private theorem transportPreserved {source target global : EnvBase} {l} (self : source.AST l)
    (extend : source.UId → target.UId) (map : target.UId → global.UId)
    (original : source.UId → global.UId) (preserves : ∀ receipt, map (extend receipt) = original receipt) :
    AST.recarrier (AST.recarrier self (.mk extend)) (.mk map) = AST.recarrier self (.mk original) := by
  rw [recarrierComp self (.mk extend) (.mk map)]
  congr 2
  funext receipt
  exact preserves receipt

private theorem typRecarrierId {base : EnvBase} (typ : base.Typ) :
    AST.recarrier typ (.mk id) = typ := by
  cases typ with
  | TLit => rfl
  | TFn input output =>
    simp only [AST.recarrier]
    rw [typRecarrierId input, typRecarrierId output]
termination_by sizeOf typ

private theorem mintedValueSame {refs : UIdRefs} [exe : ExeEnv refs] (value : refs.base.Val) :
    Val.Same (exe.uid2val.get (exe.uid2valCtx.inv (Quot.mk _ value))) value := by
  exact congrArg
    (Quot.lift (λ value : refs.base.Val => AST.recarrier value (.mk id)) (λ _ _ same => same))
    (exe.uid2valCtx.rightInv (Quot.mk _ value))

private theorem sameFnApply {source target : EnvBase} {annotation : target.Typ} {body : target.Binder .trm}
    {sourceAnnotation : source.Typ} {sourceBody : source.Binder .trm}
    (map : source.UId → target.UId)
    (same : Val.Same (.fn annotation body) (AST.recarrier (.fn sourceAnnotation sourceBody) (.mk map))) :
    ∀ receipt, Binder.apply body receipt = AST.recarrier (Pre.Binder.apply sourceBody (.inr ()))
      (.mk (Sum.elim map (λ _ => receipt))) := by
  have equality : Pre.AST.fn (AST.recarrier annotation (.mk id)) (Binder.recarrier body (.mk id)) =
      Pre.AST.fn (AST.recarrier sourceAnnotation (.mk map)) (Binder.recarrier sourceBody (.mk map)) :=
    Eq.trans same (recarrierComp (.fn sourceAnnotation sourceBody) (.mk map) (.mk id))
  have hBody := (Pre.AST.fn.inj equality).2
  intro receipt
  have canonicalApply : Binder.apply (Binder.recarrier body (.mk id)) receipt = Binder.apply body receipt :=
    applyRecarrier body id receipt
  rw [← canonicalApply, hBody, applyRecarrier]

section variable {refs : UIdRefs} [build : BuildEnv refs]

private theorem inferMonotone (trm : refs.base.Trm) (less more : Nat)
    (result : Option refs.base.Typ) (le : less ≤ more)
    (h : infer trm less = .yield result) : infer trm more = .yield result := by
  induction less generalizing more trm result with
  | zero => simp [infer] at h
  | succ less ih =>
    cases more with
    | zero => omega
    | succ more =>
      have le : less ≤ more := Nat.le_of_succ_le_succ le
      cases trm with
      | val value =>
        cases value with
        | lit repr => exact h
        | fn tIn body =>
          rw [infer] at h ⊢
          cases hb : infer (EnvBase.Binder.apply body
              (build.uid2typ.upcastK (build.uid2typCtx.inv tIn))) less with
          | outOfFuel => simp [hb, Rec.Outcome.map] at h
          | yield inferred =>
            simpa only [hb, ih _ _ _ le hb] using h
      | apply fnTerm arg =>
        rw [infer] at h ⊢
        cases hf : infer fnTerm less <;> cases ha : infer arg less
        all_goals try (simp [hf, ha] at h)
        all_goals simpa only [hf, ha, ih _ _ _ le hf, ih _ _ _ le ha] using h
      | ref carrier under =>
        rw [infer] at h ⊢
        cases lookup : refs.uid2both.get (mapRef under (.mk id) carrier) with
        | inl value =>
          simp only [lookup] at h ⊢
          exact ih _ _ _ le h
        | inr typ => simpa only [lookup] using h

private theorem inferCanonical (trm : refs.base.Trm) (fuel : Nat) :
    infer (AST.recarrier trm (.mk id)) fuel = infer trm fuel := by
  induction fuel generalizing trm with
  | zero => rfl
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => rfl
      | fn tIn body =>
        simp only [AST.recarrier]
        rw [typRecarrierId tIn]
        simp only [infer.eq_3]
        rw [applyRecarrier body id _]
        rfl
    | apply fnTerm arg => simp only [AST.recarrier, infer.eq_4, ih]
    | ref carrier under => rfl

private theorem inferValueSame (left right : refs.base.Val) (same : Val.Same left right) (fuel : Nat) :
    infer left.asTrm fuel = infer right.asTrm fuel := by
  rw [← inferCanonical left.asTrm fuel, ← inferCanonical right.asTrm fuel]
  exact congrArg (λ value : refs.base.Val => infer value.asTrm fuel) same

private theorem inferApplySuccess {fn arg : refs.base.Trm} {fuel : Nat} {typ : refs.base.Typ}
    (hInfer : infer (.apply fn arg) (fuel + 1) = .yield (some typ)) :
    ∃ input, infer fn fuel = .yield (some (.TFn input typ)) ∧
      infer arg fuel = .yield (some input) := by
  simp only [infer.eq_4] at hInfer
  repeat split at hInfer
  all_goals simp_all [LE.le]
  all_goals injection hInfer; subst_vars; exact ⟨_, rfl, rfl⟩

private theorem inferFnSuccess {annotation : refs.base.Typ} {body : refs.base.Binder .trm}
    {fuel : Nat} {typ : refs.base.Typ}
    (hInfer : infer (.val (.fn annotation body)) (fuel + 1) = .yield (some typ)) :
    ∃ output, infer (Binder.apply body (build.uid2typ.upcastK (build.uid2typCtx.inv annotation))) fuel =
      .yield (some output) ∧ typ = .TFn annotation output := by
  rw [infer.eq_3] at hInfer
  rcases hBody : infer (Binder.apply body (build.uid2typ.upcastK (build.uid2typCtx.inv annotation))) fuel
      with (_ | output) | _ <;> rw [hBody] at hInfer
  · cases hInfer
  · exact ⟨output, rfl, (Option.some.inj (Rec.Outcome.yield.inj hInfer)).symm⟩
  · cases hInfer

/-- Preserve successful inference when every source receipt remains inferable at its type. -/
private theorem inferReplace {base : EnvBase} {trm : base.Trm}
    {first second : base.UId → refs.UId} {fuel : Nat} {typ : refs.base.Typ}
    (hReplace : ∀ receipt inferred sourceFuel,
      infer (.ref (first receipt) .same) sourceFuel = .yield (some inferred) →
        ∃ targetFuel, infer (.ref (second receipt) .same) targetFuel = .yield (some inferred))
    (hInfer : infer (AST.recarrier trm (.mk first)) fuel = .yield (some typ)) :
    ∃ targetFuel, infer (AST.recarrier trm (.mk second)) targetFuel = .yield (some typ) := by
  induction fuel generalizing base trm first second typ with
  | zero => simp [infer] at hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => exact ⟨1, hInfer⟩
      | fn annotation body =>
        obtain ⟨output, hBody, hType⟩ := inferFnSuccess hInfer
        subst typ
        have inputEqual := typRecarrier annotation first second
        let receipt := build.uid2typ.upcastK (build.uid2typCtx.inv (AST.recarrier annotation (.mk first)))
        rw [applyRecarrier] at hBody
        obtain ⟨bodyFuel, hTarget⟩ := ih
          (base := ⟨base.UId ⊕ Unit⟩) (trm := Pre.Binder.apply body (.inr ()))
          (first := Sum.elim first (λ _ => receipt)) (second := Sum.elim second (λ _ => receipt))
          (by
            intro carrier inferred sourceFuel hSource
            cases carrier with
            | inl carrier => exact hReplace carrier inferred sourceFuel hSource
            | inr slot => exact ⟨sourceFuel, hSource⟩) hBody
        exact ⟨bodyFuel + 1, by
          simp only [AST.recarrier, infer.eq_3]
          rw [← inputEqual, applyRecarrier, hTarget]
          rfl⟩
    | ref carrier under =>
      have mapped : mapRef under (.mk first) carrier = first (mapRef under (.mk id) carrier) :=
        mapRefComp under (.mk id) (.mk first) carrier
      have mappedTarget : mapRef under (.mk second) carrier = second (mapRef under (.mk id) carrier) :=
        mapRefComp under (.mk id) (.mk second) carrier
      simp only [AST.recarrier, mapped] at hInfer
      obtain ⟨targetFuel, hTarget⟩ := hReplace (mapRef under (.mk id) carrier) typ (fuel + 1) hInfer
      exact ⟨targetFuel, by simpa only [AST.recarrier, mappedTarget] using hTarget⟩
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih hReplace hArg
      have hFnMore := inferMonotone _ fnFuel (max fnFuel argFuel) _ (Nat.le_max_left _ _) hFnTarget
      have hArgMore := inferMonotone _ argFuel (max fnFuel argFuel) _ (Nat.le_max_right _ _) hArgTarget
      exact ⟨max fnFuel argFuel + 1, by
        simp only [AST.recarrier, infer.eq_4, hFnMore, hArgMore]
        have hRefl : input ≤ input := rfl
        simp [hRefl]⟩

private theorem mintedTypeLookup (typ : refs.base.Typ) :
    refs.uid2both.get (build.uid2typ.upcastK (build.uid2typCtx.inv typ)) = .inr typ := by
  have lookup := build.uid2typ.equivariance (build.uid2typCtx.inv typ)
  rw [build.typeOnly, build.uid2typCtx.rightInv] at lookup
  exact lookup.symm

end

/-- Add a runtime argument receipt while retaining the enclosing source context. -/
private theorem contextExtendCompatible {refs : UIdRefs} [exe : ExeEnv refs]
    (context : RuntimeContext refs) (sourceValue : context.base.Val) (value : refs.base.Val)
    (same : Val.Same value (AST.recarrier sourceValue (.mk context.embed))) :
    let receipt := exe.uid2val.upcastK (exe.uid2valCtx.inv (Quot.mk _ value))
    let base : EnvBase := ⟨context.base.UId ⊕ Unit⟩
    let values : KVRefs base.UId base.Val := ⟨λ carrier =>
      match carrier with
      | .inl outer => AST.recarrier (context.values.get outer) (.mk Sum.inl)
      | .inr () => AST.recarrier sourceValue (.mk Sum.inl)⟩
    let embed : base.UId → refs.UId := Sum.elim context.embed (λ _ => receipt)
    ∀ carrier, (refs.uid2both.get (embed carrier)).elim
      (λ found => Val.Same found (AST.recarrier (values.get carrier) (.mk embed))) (λ _ => False) := by
  dsimp only
  intro carrier
  cases carrier with
  | inl outer =>
    dsimp only [Sum.elim]
    rw [transportPreserved (context.values.get outer) Sum.inl _ context.embed (λ _ => rfl)]
    exact context.compatible outer
  | inr slot =>
    cases slot
    dsimp only [Sum.elim]
    have lookup := exe.uid2val.equivariance (exe.uid2valCtx.inv (Quot.mk _ value))
    rw [exe.valueOnly] at lookup
    rw [← lookup]
    rw [transportPreserved sourceValue Sum.inl _ context.embed (λ _ => rfl)]
    exact Eq.trans (mintedValueSame value) same

section variable {refs : UIdRefs} [build : BuildEnv refs] [exe : ExeEnv refs]

private theorem mintedValueInfer (value : refs.base.Val) {fuel : Nat} {typ : refs.base.Typ}
    (hInfer : infer value.asTrm fuel = .yield (some typ)) :
    infer (.ref (exe.uid2val.upcastK (exe.uid2valCtx.inv (Quot.mk _ value))) .same) (fuel + 1) =
      .yield (some typ) := by
  have lookup := exe.uid2val.equivariance (exe.uid2valCtx.inv (Quot.mk _ value))
  rw [exe.valueOnly] at lookup
  simp only [infer.eq_5, mapRef, id, ← lookup]
  rw [inferValueSame _ value (mintedValueSame value)]
  exact hInfer

/-- Evaluation retains a compatible runtime source for every returned value and its captured references. -/
private theorem inferEvalSource (context : RuntimeContext refs) (trm : context.base.Trm)
    (inferFuel : Nat) (typ : refs.base.Typ)
    (hInfer : infer (AST.recarrier trm (.mk context.embed)) inferFuel = .yield (some typ))
    (evalFuel : Nat) :
    match eval (AST.recarrier trm (.mk context.embed)) evalFuel with
    | .outOfFuel => True
    | .yield none => False
    | .yield (some value) =>
      ∃ (target : RuntimeContext refs) (extend : context.base.UId → target.base.UId),
        (∀ receipt, target.embed (extend receipt) = context.embed receipt) ∧
        ∃ sourceValue : target.base.Val,
          Val.Same value (AST.recarrier sourceValue (.mk target.embed)) ∧
          ∃ valueFuel, infer value.asTrm valueFuel = .yield (some typ) := by
  induction evalFuel generalizing context trm inferFuel typ with
  | zero => trivial
  | succ evalFuel ih =>
    cases inferFuel with
    | zero => simp [infer] at hInfer
    | succ inferFuel =>
      cases trm with
      | val value => exact ⟨context, id, (λ _ => rfl), value, rfl, inferFuel + 1, hInfer⟩
      | ref carrier under =>
        let receipt := mapRef under (.mk id) carrier
        have mapped : mapRef under (.mk context.embed) carrier = context.embed receipt :=
          mapRefComp under (.mk id) (.mk context.embed) carrier
        simp only [AST.recarrier, mapped, eval.eq_4, mapRef, id]
        have compatible := context.compatible receipt
        cases lookup : refs.uid2both.get (context.embed receipt) with
        | inr annotation => simp only [lookup, Sum.elim] at compatible
        | inl value =>
          simp only [AST.recarrier, mapped, infer.eq_5, mapRef, id, lookup] at hInfer
          exact ⟨context, id, (λ _ => rfl), context.values.get receipt,
            (by simpa only [lookup, Sum.elim] using compatible), inferFuel, hInfer⟩
      | apply fn arg =>
        obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
        have safeFn := ih context fn inferFuel (.TFn input typ) hFn
        rcases fnEval : eval (AST.recarrier fn (.mk context.embed)) evalFuel with (_ | fnValue) | _
        · simp [fnEval] at safeFn
        · simp only [fnEval] at safeFn
          obtain ⟨fnContext, fnExtend, fnPreserves, sourceFn, fnSame, fnFuel, fnInfer⟩ := safeFn
          cases fnFuel with
          | zero => simp [infer] at fnInfer
          | succ fnFuel =>
            cases fnValue with
            | lit repr =>
              simp only [Val.asTrm, infer.eq_2, Rec.Outcome.yield.injEq] at fnInfer
              cases fnInfer
            | fn annotation body =>
              obtain ⟨output, hBody, fnType⟩ := inferFnSuccess fnInfer
              obtain ⟨inputEqual, outputEqual⟩ := Pre.AST.TFn.inj fnType
              subst annotation
              subst output
              cases sourceFn with
              | lit repr =>
                simp only [Val.Same, AST.recarrier] at fnSame
                cases fnSame
              | fn sourceAnnotation sourceBody =>
                have bodyEqual := sameFnApply fnContext.embed fnSame
                let liftedArg : fnContext.base.Trm := AST.recarrier arg (.mk fnExtend)
                have argTransport : AST.recarrier liftedArg (.mk fnContext.embed) =
                    AST.recarrier arg (.mk context.embed) :=
                  transportPreserved arg fnExtend fnContext.embed context.embed fnPreserves
                have safeArg := ih fnContext liftedArg inferFuel input (by rw [argTransport]; exact hArg)
                rw [argTransport] at safeArg
                rcases argEval : eval (AST.recarrier arg (.mk context.embed)) evalFuel with (_ | argValue) | _
                · simp [argEval] at safeArg
                · simp only [argEval] at safeArg
                  obtain ⟨argContext, argExtend, argPreserves, sourceArg, argSame, argFuel, argTyped⟩ := safeArg
                  let receipt := exe.uid2val.upcastK (exe.uid2valCtx.inv (Quot.mk _ argValue))
                  let extended : RuntimeContext refs :=
                    { base := ⟨argContext.base.UId ⊕ Unit⟩
                      values := ⟨λ carrier =>
                        match carrier with
                        | .inl outer => AST.recarrier (argContext.values.get outer) (.mk Sum.inl)
                        | .inr () => AST.recarrier sourceArg (.mk Sum.inl)⟩
                      embed := Sum.elim argContext.embed (λ _ => receipt)
                      compatible := contextExtendCompatible argContext sourceArg argValue argSame }
                  let sourceTerm := Pre.Binder.apply sourceBody (.inr ())
                  let bodyTerm : extended.base.Trm := AST.recarrier sourceTerm (.mk (Sum.map argExtend id))
                  have bodyTransport : AST.recarrier bodyTerm (.mk extended.embed) =
                      AST.recarrier sourceTerm (.mk (Sum.elim fnContext.embed (λ _ => receipt))) :=
                    transportPreserved sourceTerm (Sum.map argExtend id) extended.embed _ (by
                      intro carrier
                      cases carrier with
                      | inl outer => exact argPreserves outer
                      | inr slot => rfl)
                  let typeReceipt := build.uid2typ.upcastK (build.uid2typCtx.inv input)
                  change infer (AST.recarrier (Pre.Binder.apply body (.inr ()))
                    (.mk (Sum.elim id (λ _ => typeReceipt)))) fnFuel = _ at hBody
                  obtain ⟨bodyFuel, runtimeBody⟩ := inferReplace
                    (base := ⟨refs.UId ⊕ Unit⟩) (trm := Pre.Binder.apply body (.inr ()))
                    (second := Sum.elim id (λ _ => receipt))
                    (by
                      intro carrier inferred sourceFuel hSource
                      cases carrier with
                      | inl outer => exact ⟨sourceFuel, hSource⟩
                      | inr slot =>
                        cases sourceFuel with
                        | zero => simp [infer] at hSource
                        | succ sourceFuel =>
                          simp only [infer.eq_5, mapRef, id, Sum.elim, typeReceipt,
                            mintedTypeLookup input] at hSource
                          have inferredEqual : input = inferred := Option.some.inj (Rec.Outcome.yield.inj hSource)
                          subst inferred
                          exact ⟨argFuel + 1, mintedValueInfer argValue argTyped⟩) hBody
                  change infer (Binder.apply body receipt) bodyFuel = _ at runtimeBody
                  have bodyEvalTransport : Binder.apply body receipt =
                      AST.recarrier bodyTerm (.mk extended.embed) :=
                    (bodyEqual receipt).trans bodyTransport.symm
                  have safeBody := ih extended bodyTerm bodyFuel typ (by rw [← bodyEvalTransport]; exact runtimeBody)
                  simp only [AST.recarrier, eval.eq_3, fnEval, argEval]
                  rw [bodyEvalTransport]
                  rcases bodyEval : eval (AST.recarrier bodyTerm (.mk extended.embed)) evalFuel with (_ | result) | _
                  · simp [bodyEval] at safeBody
                  · simp only [bodyEval] at safeBody
                    obtain ⟨target, bodyExtend, bodyPreserves, sourceResult, resultSame,
                      resultFuel, resultTyped⟩ := safeBody
                    refine ⟨target, (λ receipt => bodyExtend (.inl (argExtend (fnExtend receipt)))),
                      ?_, sourceResult, resultSame, resultFuel, resultTyped⟩
                    intro outer
                    rw [bodyPreserves]
                    exact (argPreserves (fnExtend outer)).trans (fnPreserves outer)
                  · trivial
                · simp [AST.recarrier, eval.eq_3, fnEval, argEval]
        · cases eval (AST.recarrier arg (.mk context.embed)) evalFuel <;>
            simp [AST.recarrier, eval.eq_3, fnEval]

/-- Successful inference makes the same transported runtime source term safe.

The context premise is required: compile-time type receipts alone cannot be evaluated as values.
-/
theorem fundamental (context : RuntimeContext refs) (trm : context.base.Trm)
    (fuel : Nat) (typ : refs.base.Typ)
    (hInfer : infer (refs := refs) (AST.recarrier trm (.mk context.embed)) fuel = .yield (some typ)) :
    Safety (AST.recarrier trm (.mk context.embed)) typ := by
  intro evalFuel
  have safe := inferEvalSource context trm fuel typ hInfer evalFuel
  rcases result : eval (AST.recarrier trm (.mk context.embed)) evalFuel with (_ | value) | _
  · simp [result] at safe
  · simp only [result] at safe
    obtain ⟨_, _, _, _, _, valueFuel, typed⟩ := safe
    exact ⟨valueFuel, by rw [typed]; exact (rfl : typ ≤ typ)⟩
  · trivial

end
end Lp2lc.Active.STLC
