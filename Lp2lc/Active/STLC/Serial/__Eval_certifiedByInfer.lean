import «Lp2lc».Active.STLC.Serial.__Infer

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util

namespace CertifiedByInfer

abbrev ConditionalVal (condition : Typ -> Prop) := {v : ExeValue // (v.value.asTrm.infer v.captured).isDecidable condition}

/-- A returned value certified at the caller's independently inferred type. -/
abbrev CertifiedVal (typ : Typ) := ConditionalVal (λ _t => _t = typ)

/-- Fuel-bounded certified evaluation may still exhaust its fuel. -/
abbrev Result (typ : Typ) := Rec (CertifiedVal typ)

variable {n fuel : Nat} {typ : Typ} {entries : CompilerBindings}

private theorem inferWitness {self : RecOpt Typ} {condition : Typ → Prop}
    (hInfer : self.isDecidable condition) (hZero : self 0 = .outOfFuel) :
    ∃ fuel typ, self (fuel + 1) = .yield (some typ) ∧ condition typ := by
  obtain ⟨fuel, hInfer⟩ := hInfer
  cases fuel with
  | zero => simp_all
  | succ fuel =>
    cases hResult : self (fuel + 1) <;> (try cases ‹Option Typ›) <;> simp_all
    exact ⟨fuel, _, hResult, hInfer⟩

private theorem inferApplySuccess {fn arg : Trm n}
    (hInfer : inferInternal (.apply fn arg) entries (fuel + 1) = .yield (some typ)) :
    ∃ input, inferInternal fn entries fuel = .yield (some (.TFn input typ)) ∧
      inferInternal arg entries fuel = .yield (some input) := by
  simp only [inferInternal.eq_5] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals injection hInfer; subst_vars; exact ⟨_, rfl, rfl⟩

private theorem inferFnSuccess {annotation : Typ n} {body : Binder n .trm}
    (hInfer : inferInternal (.val (.fn annotation body)) entries (fuel + 1) = .yield (some typ)) :
    let input := resolveType annotation
    ∃ output, inferInternal (body.apply .only)
        (entries.set (n + 1) (.inr input)) fuel = .yield (some output) ∧
      typ = .TFn input output := by
  cases hBody : inferInternal (body.apply .only)
      (entries.set (n + 1) (.inr (resolveType annotation))) fuel <;>
    (try cases ‹Option Typ›) <;> simp_all [inferInternal.eq_3, Rec.Outcome.map, Option.map]
  exact ⟨_, rfl, (Option.some.inj hInfer).symm⟩

-- Certification reuses inference monotonicity and derives its other inference facts locally.
private def entryFits (entry : Option ValOrTyp) (typ : Typ) : Prop :=
  ∃ fuel,
    (match entry with
    | some (.inl (.mk _ value captured)) => inferInternal value.asTrm (captured.map .inl) fuel
    | some (.inr input) => .yield (some input)
    | none => .yield none) = .yield (some typ)

/-- Replacing hypothetical entries by inferable runtime values preserves inference. -/
private theorem inferReplace {trm : Trm n} {source target : CompilerBindings}
    (hReplace : ∀ index typ, entryFits (source index) typ → entryFits (target index) typ)
    (hInfer : inferInternal trm source fuel = .yield (some typ)) :
    ∃ targetFuel, inferInternal trm target targetFuel = .yield (some typ) := by
  induction fuel generalizing n trm source target typ with
  | zero => cases hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => exact ⟨1, by simpa only [inferInternal.eq_2] using hInfer⟩
      | fn annotation body =>
        obtain ⟨output, hBody, hType⟩ := inferFnSuccess hInfer
        subst typ
        obtain ⟨bodyFuel, hTarget⟩ := ih (target := target.set (n + 1) (.inr (resolveType annotation)))
          (by intro index inputTyp; simp only [NatBindings.set, List.lookup]; split <;> simp_all) hBody
        exact ⟨bodyFuel + 1, by simp only [inferInternal.eq_3, hTarget, Rec.Outcome.map]; rfl⟩
    | ref carrier under =>
      obtain ⟨targetFuel, hTarget⟩ := hReplace under.sourceIndex.down typ
        ⟨fuel, by
          simp only [inferInternal.eq_4] at hInfer
          split at hInfer <;> simp_all⟩
      exact ⟨targetFuel + 1, by
        simp only [inferInternal.eq_4]
        split <;> simp_all [entryFits]⟩
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih hReplace hArg
      have hFnMore := Monotone.termInfer fn target fnFuel (max fnFuel argFuel) _
        (Nat.le_max_left _ _) hFnTarget
      have hArgMore := Monotone.termInfer arg target argFuel (max fnFuel argFuel) _
        (Nat.le_max_right _ _) hArgTarget
      exact ⟨max fnFuel argFuel + 1, by
        simp only [inferInternal.eq_5, hFnMore, hArgMore]
        exact congrArg _ (ite_eq_left (rfl : input = input))⟩

/-- Each recursive call accepts successful inference and yields an unconditionally certified value. -/
private def evalInternal {n} (self : Trm n) (bindings : ExeBindings) (condition : Typ → Prop)
    (hInfer : (self.infer bindings).isDecidable condition) :
    Rec (ConditionalVal condition) := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield ⟨.mk n value bindings, hInfer⟩
    | .ref _ under =>
      match hBinding : bindings under.sourceIndex.down with
      | none => False.elim (by
          obtain ⟨inferFuel, hInfer⟩ := hInfer
          cases inferFuel <;> simp [infer, inferInternal, NatBindings.getMap, hBinding] at hInfer)
      | some (.mk context value captured) => .yield ⟨.mk context value captured, by
          obtain ⟨inferFuel, typ, hInfer, hCondition⟩ := inferWitness hInfer rfl
          simp only [infer, inferInternal.eq_4, NatBindings.getMap, hBinding, Option.map] at hInfer
          exact ⟨inferFuel, by simp only [infer, hInfer]; exact hCondition⟩⟩
    | .apply fn arg =>
      let fnCondition := λ fnTyp => ∃ input output, fnTyp = .TFn input output ∧
        (infer arg bindings).isDecidable (λ inferred => inferred = input) ∧ condition output
      have fnTyped : (infer fn bindings).isDecidable fnCondition := by
        obtain ⟨inferFuel, typ, hInfer, hCondition⟩ := inferWitness hInfer rfl
        obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
        exact ⟨inferFuel, by
          simp only [infer, hFn]
          exact ⟨input, typ, rfl, ⟨inferFuel, by simp only [infer, hArg]; rfl⟩, hCondition⟩⟩
      (evalInternal fn bindings fnCondition fnTyped fuel).flatMap (λ fnResult =>
        match fnResult with
        | ⟨.mk _ (.lit _) _, fnSafe⟩ => False.elim (by
            obtain ⟨fnFuel, _, hFn, input, output, rfl, _, _⟩ := inferWitness fnSafe rfl
            simp [infer, Val.asTrm, inferInternal] at hFn
            cases Option.some.inj hFn)
        | ⟨.mk context (.fn annotation body) captured, fnSafe⟩ =>
          have fnFacts : (infer arg bindings).isDecidable (λ inferred => inferred = resolveType annotation) ∧
              (inferInternal (body.apply .only)
                ((captured.map .inl).set (context + 1) (.inr (resolveType annotation)))).isDecidable condition := by
            obtain ⟨fnFuel, _, hFn, input, output, rfl, hArg, hCondition⟩ := inferWitness fnSafe rfl
            obtain ⟨fnOutput, hBody, hFnType⟩ := inferFnSuccess hFn
            rcases Pre.AST.TFn.inj hFnType with ⟨rfl, rfl⟩
            exact ⟨hArg, ⟨fnFuel, by simp only [hBody]; exact hCondition⟩⟩
          (evalInternal arg bindings _ fnFacts.1 fuel).flatMap (λ argResult =>
            let bodyBindings := captured.set (context + 1) argResult.val
            have bodyTyped : (infer (body.apply .only) bodyBindings).isDecidable condition := by
              rcases argResult with ⟨⟨argContext, argValue, argCaptured⟩, argSafe⟩
              obtain ⟨bodyFuel, output, hBody, hCondition⟩ := inferWitness fnFacts.2 rfl
              obtain ⟨argInferFuel, _, hArg, rfl⟩ := inferWitness argSafe rfl
              obtain ⟨targetFuel, hTarget⟩ := inferReplace (target := bodyBindings.map .inl)
                (by
                  have typedArg : entryFits (some (.inl (.mk _ argValue argCaptured))) (resolveType annotation) :=
                    ⟨argInferFuel + 1, hArg⟩
                  intro index inputTyp hSource
                  simp only [bodyBindings, NatBindings.getMap, NatBindings.set, List.lookup] at hSource ⊢
                  split at hSource <;> simp_all [entryFits]) hBody
              exact ⟨targetFuel, by simp only [infer, hTarget]; exact hCondition⟩
            evalInternal (body.apply .only) bodyBindings condition bodyTyped fuel))

end CertifiedByInfer

open CertifiedByInfer

/-- Evaluate an independently inferred term with an erased safety proof at every recursive step. -/
def eval_certified {n} (self : Trm n) (bindings : ExeBindings := .empty)
    {inferFuel : Nat} {typ : Typ}
    (hInfer : self.infer bindings inferFuel = .yield (some typ)) : Result typ := λ fuel =>
  (evalInternal self bindings (λ inferred => inferred = typ)
    ⟨inferFuel, by simp only [hInfer]; rfl⟩ fuel).map (λ result => ⟨result.val, result.property⟩)

end Lp2lc.Active.STLC.AST
