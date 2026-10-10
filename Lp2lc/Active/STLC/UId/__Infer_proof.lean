import «Lp2lc».Active.STLC.UId.__Infer

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util Root Root.Trm

section variable {refs : UIdRefs} [build : BuildEnv refs] [exe : ExeEnv refs]

/-- Every completed evaluation succeeds, and its value can be inferred at the claimed type. -/
def Safety (trm : refs.base.Trm) (typ : refs.base.Typ) : Prop :=
  trm.eval.isSemiDecidable
    (λ value => value.asTrm.infer.isDecidable (λ inferred => inferred ≤ typ))

end

section variable {refs : UIdRefs} [build : BuildEnv refs]

private theorem typRecarrier {source target : Root} (typ : source.Typ)
    (first second : source.UId → target.UId) :
    AST.recarrier typ first = AST.recarrier typ second := by
  cases typ with
  | TLit => rfl
  | TFn input output =>
    change Pre.AST.TFn _ _ = Pre.AST.TFn _ _
    exact congr (congrArg Pre.AST.TFn (typRecarrier input first second)) (typRecarrier output first second)
termination_by sizeOf typ

private theorem typRecarrierId {base : Root} (typ : base.Typ) :
    AST.recarrier typ id = typ := by
  cases typ with
  | TLit => rfl
  | TFn input output =>
    exact congr (congrArg Pre.AST.TFn (typRecarrierId input)) (typRecarrierId output)
termination_by sizeOf typ

private theorem typRecarrierComp {source middle target : Root} (typ : source.Typ)
    (first : source.UId → middle.UId) (second : middle.UId → target.UId) :
    AST.recarrier (AST.recarrier typ first) second =
      AST.recarrier typ (second ∘ first) := by
  cases typ with
  | TLit => rfl
  | TFn input output =>
    exact congr (congrArg Pre.AST.TFn (typRecarrierComp input first second))
      (typRecarrierComp output first second)
termination_by sizeOf typ

private theorem inferTransport {source target : Root} (trm : source.Trm)
    (map : source.UId → target.UId) (bindings : target.UId → refs.UId ⊕ refs.UId) (fuel : Nat) :
    infer.visit (AST.recarrier trm map) bindings fuel =
      infer.visit trm (bindings ∘ map) fuel := by
  induction fuel generalizing source target trm map bindings with
  | zero => rfl
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => rfl
      | fn annotation body =>
        cases body
        rename_i body
        change infer.visit (.val (.fn (AST.recarrier annotation map)
            (.mk (λ _ => AST.recarrier (body (.inr ())) (Sum.map map id))))) bindings (fuel + 1) = _
        simp only [infer.visit.eq_3, Pre.Binder.apply, Pre.Binder.mk]
        rw [typRecarrierComp, ih (body (.inr ())) (Sum.map map id)]
        congr 2
        funext carrier
        cases carrier <;> rfl
    | apply fn arg =>
      change infer.visit (.apply (AST.recarrier fn map) (AST.recarrier arg map)) bindings (fuel + 1) = _
      simp only [infer.visit.eq_4, ih]
    | ref carrier under =>
      change infer.visit (.ref (map (mapRef under carrier)) .same) bindings (fuel + 1) = _
      rfl

private theorem inferMonotone {base : Root} (trm : base.Trm)
    (bindings : base.UId → refs.UId ⊕ refs.UId) (less more : Nat)
    (result : Option refs.base.Typ) (le : less ≤ more)
    (h : infer.visit trm bindings less = .yield result) :
    infer.visit trm bindings more = .yield result := by
  induction less generalizing base trm bindings more result with
  | zero => simp [infer.visit] at h
  | succ less ih =>
    cases more with
    | zero => omega
    | succ more =>
      have le := Nat.le_of_succ_le_succ le
      cases trm <;> try cases ‹Pre.AST _ .val›
      all_goals
        simp only [infer.visit.eq_2, infer.visit.eq_3, infer.visit.eq_4, infer.visit.eq_5,
          Rec.Outcome.map] at h ⊢
        repeat split at h
        all_goals simp_all

private theorem mintedTypeLookup (typ : refs.base.Typ) :
    refs.uid2both.get (build.uid2bothCtx.inv (.inl typ)) = .inl typ := by
  exact build.uid2bothCtx.rightInv (.inl typ)

private theorem inferApplySuccess {base : Root} {fn arg : base.Trm}
    {bindings : base.UId → refs.UId ⊕ refs.UId} {fuel : Nat} {typ : refs.base.Typ}
    (hInfer : infer.visit (.apply fn arg) bindings (fuel + 1) = .yield (some typ)) :
    ∃ input, infer.visit fn bindings fuel = .yield (some (.TFn input typ)) ∧
      infer.visit arg bindings fuel = .yield (some input) := by
  simp only [infer.visit.eq_4] at hInfer
  repeat split at hInfer
  all_goals simp_all [LE.le]
  all_goals injection hInfer; subst_vars; exact ⟨_, rfl, rfl⟩

private theorem inferFnSuccess {base : Root} {annotation : base.Typ} {body : base.Binder .trm}
    {bindings : base.UId → refs.UId ⊕ refs.UId} {fuel : Nat} {typ : refs.base.Typ}
    (hInfer : infer.visit (.val (.fn annotation body)) bindings (fuel + 1) = .yield (some typ)) :
    let input := AST.recarrier annotation (Sum.elim id id ∘ bindings)
    ∃ output, infer.visit (base := ⟨base.UId ⊕ Unit⟩) (Pre.Binder.apply body (.inr ()))
        (Sum.elim bindings (λ _ => .inl (build.uid2bothCtx.inv (.inl input)))) fuel = .yield (some output) ∧
      typ = .TFn input output := by
  dsimp only
  rcases hBody : infer.visit (base := ⟨base.UId ⊕ Unit⟩) (Pre.Binder.apply body (.inr ()))
      (Sum.elim bindings (λ _ => .inl (build.uid2bothCtx.inv
        (.inl (AST.recarrier annotation (Sum.elim id id ∘ bindings)))))) fuel with (_ | output) | _
  all_goals simp only [infer.visit.eq_3, hBody, Rec.Outcome.map, Option.map,
    Rec.Outcome.yield.injEq] at hInfer
  all_goals try cases hInfer
  exact ⟨output, rfl, rfl⟩

private theorem inferReplace {base : Root} {trm : base.Trm}
    {first second : base.UId → refs.UId ⊕ refs.UId} {fuel : Nat} {typ : refs.base.Typ}
    (hReplace : ∀ receipt inferred sourceFuel,
      infer.visit (.ref receipt .same) first sourceFuel = .yield (some inferred) →
        ∃ targetFuel, infer.visit (.ref receipt .same) second targetFuel = .yield (some inferred))
    (hInfer : infer.visit trm first fuel = .yield (some typ)) :
    ∃ targetFuel, infer.visit trm second targetFuel = .yield (some typ) := by
  induction fuel generalizing base trm first second typ with
  | zero => simp [infer.visit] at hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => exact ⟨1, hInfer⟩
      | fn annotation body =>
        obtain ⟨output, hBody, hType⟩ := inferFnSuccess hInfer
        subst typ
        have inputEqual := typRecarrier annotation (Sum.elim id id ∘ first) (Sum.elim id id ∘ second)
        let input := AST.recarrier annotation (Sum.elim id id ∘ first)
        let receipt := build.uid2bothCtx.inv (.inl input)
        obtain ⟨bodyFuel, hTarget⟩ := ih
          (base := ⟨base.UId ⊕ Unit⟩) (trm := Pre.Binder.apply body (.inr ()))
          (first := Sum.elim first (λ _ => .inl receipt))
          (second := Sum.elim second (λ _ => .inl receipt))
          (by
            intro carrier inferred sourceFuel hSource
            cases carrier with
            | inl outer =>
              have original : infer.visit (base := base) (.ref outer .same) first sourceFuel =
                  .yield (some inferred) := (inferTransport (source := base) (target := ⟨base.UId ⊕ Unit⟩)
                (.ref (P' := base.P) outer .same) Sum.inl
                (Sum.elim first (λ _ => .inl receipt)) sourceFuel).symm.trans hSource
              obtain ⟨targetFuel, hTarget⟩ := hReplace outer inferred sourceFuel original
              exact ⟨targetFuel, (inferTransport (source := base) (target := ⟨base.UId ⊕ Unit⟩)
                (.ref (P' := base.P) outer .same) Sum.inl
                (Sum.elim second (λ _ => .inl receipt)) targetFuel).trans hTarget⟩
            | inr slot => exact ⟨sourceFuel, by cases sourceFuel <;> exact hSource⟩) hBody
        exact ⟨bodyFuel + 1, by
          rw [infer.visit.eq_3, ← inputEqual, hTarget]
          rfl⟩
    | ref carrier under =>
      have canonical := (inferTransport (.ref carrier under) id first (fuel + 1)).trans hInfer
      obtain ⟨targetFuel, hTarget⟩ := hReplace (mapRef under carrier) typ (fuel + 1) canonical
      exact ⟨targetFuel, (inferTransport (.ref carrier under) id second targetFuel).symm.trans hTarget⟩
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih hReplace hArg
      have hFnMore := inferMonotone fn second fnFuel (max fnFuel argFuel) _ (Nat.le_max_left _ _) hFnTarget
      have hArgMore := inferMonotone arg second argFuel (max fnFuel argFuel) _ (Nat.le_max_right _ _) hArgTarget
      exact ⟨max fnFuel argFuel + 1, by
        simp only [infer.visit.eq_4, hFnMore, hArgMore]
        have hRefl : input ≤ input := rfl
        simp [hRefl]⟩

variable [exe : ExeEnv refs]

private theorem mintedValueInfer (value : refs.base.Val) {fuel : Nat} {typ : refs.base.Typ}
    (hInfer : infer value.asTrm fuel = .yield (some typ)) :
    infer (.ref (exe.uid2valCtx.inv (canonicalVal value)).val .same) (fuel + 1) =
      .yield (some typ) := by
  have lookup : refs.uid2both.get (exe.uid2valCtx.inv (canonicalVal value)).val =
      .inr (canonicalVal value) :=
    (Sum.inr_getRight _ _).symm.trans
      (congrArg Sum.inr (exe.uid2valCtx.rightInv (canonicalVal value)))
  simp only [infer, infer.visit.eq_5, mapRef, Sum.elim, id, lookup]
  exact (inferTransport value.asTrm id Sum.inr fuel).trans hInfer

private theorem inferEvalSafety (trm : refs.base.Trm) (inferFuel : Nat) (typ : refs.base.Typ)
    (hInfer : infer trm inferFuel = .yield (some typ)) :
    (eval trm).isSemiDecidable (λ result =>
      ∃ valueFuel, infer result.asTrm valueFuel = .yield (some typ)) := by
  intro evalFuel
  induction evalFuel generalizing trm inferFuel typ with
  | zero => trivial
  | succ evalFuel ih =>
    cases inferFuel with
    | zero => simp [infer, infer.visit] at hInfer
    | succ inferFuel =>
      cases trm with
      | val value => exact ⟨inferFuel + 1, hInfer⟩
      | ref carrier under =>
        cases lookup : refs.uid2both.get (mapRef under carrier) with
        | inl input =>
          simp only [infer, infer.visit.eq_5, Sum.elim, id, lookup] at hInfer
          cases hInfer
        | inr value =>
          simp only [infer, infer.visit.eq_5, Sum.elim, id, lookup] at hInfer
          simp only [eval.eq_4, lookup]
          exact ⟨inferFuel, hInfer⟩
      | apply fn arg =>
        obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
        have hFnSafety := ih fn inferFuel (.TFn input typ) hFn
        have hArgSafety := ih arg inferFuel input hArg
        cases hFnEval : eval fn evalFuel <;> try cases ‹Option refs.base.Val›
        all_goals simp [hFnEval] at hFnSafety
        case outOfFuel =>
          cases eval arg evalFuel <;> simp [eval.eq_3, hFnEval]
        case yield.some fnValue =>
          obtain ⟨fnInferFuel, hFnValue⟩ := hFnSafety
          cases fnInferFuel with
          | zero => simp [infer, infer.visit] at hFnValue
          | succ fnInferFuel =>
            cases fnValue with
            | lit repr =>
              simp only [Val.asTrm, infer, infer.visit.eq_2, Rec.Outcome.yield.injEq] at hFnValue
              cases Option.some.inj hFnValue
            | fn annotation body =>
              cases hArgEval : eval arg evalFuel <;> try cases ‹Option refs.base.Val›
              all_goals simp [hArgEval] at hArgSafety
              case outOfFuel => simp [eval.eq_3, hFnEval, hArgEval]
              case yield.some argValue =>
                obtain ⟨argInferFuel, hArgValue⟩ := hArgSafety
                obtain ⟨fnOutput, hBody, hFnType⟩ := inferFnSuccess hFnValue
                have annotationId : AST.recarrier annotation (Sum.elim id id ∘ Sum.inr) = annotation :=
                  typRecarrierId annotation
                rw [annotationId] at hFnType hBody
                rcases Pre.AST.TFn.inj hFnType with ⟨hInput, hOutput⟩
                subst fnOutput
                rw [← hInput] at hBody
                let receipt := (exe.uid2valCtx.inv (canonicalVal argValue)).val
                obtain ⟨bodyFuel, hBodyTarget⟩ := inferReplace
                  (second := Sum.inr ∘ Sum.elim id (λ _ => receipt))
                  (by
                    intro carrier inferred sourceFuel hSource
                    cases carrier with
                    | inl outer => exact ⟨sourceFuel, by cases sourceFuel <;> exact hSource⟩
                    | inr slot =>
                      cases sourceFuel with
                      | zero => cases hSource
                      | succ sourceFuel =>
                        simp only [infer.visit.eq_5, mapRef, Sum.elim, mintedTypeLookup, id] at hSource
                        have equality := Option.some.inj (Rec.Outcome.yield.inj hSource)
                        subst inferred
                        exact ⟨argInferFuel + 1, mintedValueInfer argValue hArgValue⟩) hBody
                have hRuntimeBody : infer (Binder.apply body receipt) bodyFuel = .yield (some typ) :=
                  (inferTransport (Pre.Binder.apply body (.inr ())) (Sum.elim id (λ _ => receipt))
                    Sum.inr bodyFuel).trans hBodyTarget
                simpa only [eval.eq_3, hFnEval, hArgEval] using
                  ih (Binder.apply body receipt) bodyFuel typ hRuntimeBody

namespace Fundamental

/-- Successful runtime inference excludes evaluation rejection and preserves the result's type. -/
theorem main (trm : refs.base.Trm) (fuel : Nat) (typ : refs.base.Typ)
    (hInfer : trm.infer fuel = .yield (some typ)) : Safety trm typ := by
  intro evalFuel
  have safe := inferEvalSafety trm fuel typ hInfer evalFuel
  rcases result : eval trm evalFuel with (_ | value) | _
  · simp [result] at safe
  · simp only [result] at safe
    obtain ⟨valueFuel, typed⟩ := safe
    exact ⟨valueFuel, by rw [typed]; exact (rfl : typ ≤ typ)⟩
  · trivial

end Fundamental

end
end Lp2lc.Active.STLC
