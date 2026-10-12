import «Lp2lc».Active.STLC.UId.__Infer

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util Root Root.Trm

/-- Runtime references and their stored values are valid; lexical binder slots are admitted separately. -/
inductive runtimeRefs (refs : UIdRefs) : {base : Root} →
    (origins : base.UId → refs.UId ⊕ Unit) → (trm : base.Trm) → Prop where
  | lit {base origins repr} : runtimeRefs refs (base := base) origins (.val (.lit repr))
  | fn {base : Root} {origins annotation} {body : base.Binder .trm}
      (runtime : runtimeRefs refs (base := ⟨base.UId ⊕ Unit⟩) (Sum.elim origins (λ _ => .inr ()))
        (Pre.Binder.apply body (.inr ()))) :
      runtimeRefs refs (base := base) origins (.val (.fn annotation body))
  | apply {base origins fn arg}
      (runtimeFn : runtimeRefs refs (base := base) origins fn) (runtimeArg : runtimeRefs refs origins arg) :
      runtimeRefs refs origins (.apply fn arg)
  | bound {base origins carrier under} (origin : origins (mapRef under carrier) = .inr ()) :
      runtimeRefs refs (base := base) origins (.ref carrier under)
  | value {base origins carrier under receipt value}
      (origin : origins (mapRef under carrier) = .inl receipt) (lookup : refs.uid2both.get receipt = .inr value)
      (runtime : runtimeRefs refs Sum.inl value.asTrm) :
      runtimeRefs refs (base := base) origins (.ref carrier under)

section variable {refs : UIdRefs} [build : BuildEnv refs]

/-- Every completed evaluation succeeds, and its value can be inferred at the claimed type. -/
def safety (trm : refs.base.Trm) (typ : refs.base.Typ) : Prop :=
  trm.eval.isSemiDecidable
    (λ value => value.asTrm.infer.isDecidable (λ inferred => inferred = typ))

end

namespace Fundamental

section variable {refs : UIdRefs} [build : BuildEnv refs]

private theorem typRecarrier {source target : Root} (typ : source.Typ)
    (first second : source.UId → target.UId) :
    AST.recarrier typ first = AST.recarrier typ second := by
  cases typ <;> try rfl
  change Pre.AST.TFn _ _ = Pre.AST.TFn _ _
  exact congr (congrArg Pre.AST.TFn (typRecarrier _ first second)) (typRecarrier _ first second)
termination_by sizeOf typ

private theorem recarrierComp {source middle target : Root} {l} (self : source.AST l)
    (first : source.UId → middle.UId) (second : middle.UId → target.UId) :
    AST.recarrier (AST.recarrier self first) second =
      AST.recarrier self (second ∘ first) := visit self rfl first second
where
  visit {P l I J} (self : Pre.AST P l) (encoding : P.I = .FreeOrUnit)
      (first : P.TRef → I) (second : I → J) :
      AST.recarrier.visit (AST.recarrier.visit self encoding first) rfl second =
        AST.recarrier.visit self encoding (second ∘ first) := by
    induction self using Pre.AST.rec
        (motive_1 := λ P l body => ∀ carrier (encoding : P.Next.I = .FreeOrUnit)
          {I J} (first : P.Next.TRef → I) (second : I → J),
          AST.recarrier.visit (AST.recarrier.visit (Pre.Binder.apply body carrier) encoding first) rfl second =
            AST.recarrier.visit (Pre.Binder.apply body carrier) encoding (second ∘ first))
        generalizing I J with
    | TLit => rfl
    | TFn input output ihInput ihOutput =>
      exact congr (congrArg Pre.AST.TFn (ihInput encoding first second)) (ihOutput encoding first second)
    | lit repr => rfl
    | @fn P annotation body ihInput ihBody =>
      rcases body with ⟨body⟩
      rcases P with ⟨B, _, _⟩
      cases encoding
      change Pre.AST.fn _ (.mk (λ _ => _)) = Pre.AST.fn _ (.mk (λ _ => _))
      rw [ihInput rfl first second]
      congr 2
      funext carrier
      change AST.recarrier.visit (AST.recarrier.visit (body (.inr ())) rfl (Sum.map first id))
        rfl (Sum.map second id) = _
      refine (ihBody (.inr ()) rfl (Sum.map first id) (Sum.map second id)).trans ?_
      exact congrArg (AST.recarrier.visit (body (.inr ())) rfl) (Sum.map_comp_map second id first id)
    | val value ih => exact congrArg Pre.AST.val (ih encoding first second)
    | apply fn arg ihFn ihArg =>
      exact congr (congrArg Pre.AST.apply (ihFn encoding first second)) (ihArg encoding first second)
    | ref carrier under => rfl
    | _ body ih => exact ih _ _ _ _

private theorem recarrierFn {source target : Root} (annotation : source.Typ) (body : source.Binder .trm)
    (map : source.UId → target.UId) :
    AST.recarrier (.val (.fn annotation body)) map = .val (.fn (AST.recarrier annotation map)
      (.mk (λ _ => AST.recarrier (Pre.Binder.apply body (.inr ())) (Sum.map map id)))) := by
  cases body
  rfl

private theorem inferApplySuccess {fn arg : refs.base.Trm} {fuel : Nat} {typ : refs.base.Typ}
    (hInfer : infer (.apply fn arg) (fuel + 1) = .yield (some typ)) :
    ∃ input, infer fn fuel = .yield (some (.TFn input typ)) ∧
      infer arg fuel = .yield (some input) := by
  simp only [infer.eq_4] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals injection hInfer; subst_vars; exact ⟨_, rfl, rfl⟩

private theorem inferFnSuccess {annotation : refs.base.Typ} {body : refs.base.Binder .trm}
    {fuel : Nat} {typ : refs.base.Typ}
    (hInfer : infer (.val (.fn annotation body)) (fuel + 1) = .yield (some typ)) :
    ∃ output, infer (Binder.apply body (build.uid2bothCtx.inv (.inl annotation))) fuel = .yield (some output) ∧
      typ = .TFn annotation output := by
  rcases hBody : infer (Binder.apply body (build.uid2bothCtx.inv (.inl annotation))) fuel with
      (_ | output) | _
  all_goals simp [infer.eq_3, hBody, Rec.Outcome.map, Option.map] at hInfer
  exact ⟨output, rfl, Option.some.inj hInfer.symm⟩

private theorem inferReplace {base : Root} {trm : base.Trm}
    {first second : base.UId → refs.UId} {fuel : Nat} {typ : refs.base.Typ}
    (hReplace : ∀ receipt inferred sourceFuel,
      infer (.ref (first receipt) .same) sourceFuel = .yield (some inferred) →
        ∃ targetFuel, infer (.ref (second receipt) .same) targetFuel = .yield (some inferred))
    (hInfer : infer (AST.recarrier trm first) fuel = .yield (some typ)) :
    ∃ targetFuel, infer (AST.recarrier trm second) targetFuel = .yield (some typ) := by
  induction fuel generalizing base trm first second typ with
  | zero => simp [infer] at hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => exact ⟨1, hInfer⟩
      | fn annotation body =>
        rw [recarrierFn] at hInfer
        obtain ⟨output, hBody, hType⟩ := inferFnSuccess hInfer
        subst typ
        have inputEqual := typRecarrier annotation first second
        let input := AST.recarrier annotation first
        let receipt := build.uid2bothCtx.inv (.inl input)
        change infer (AST.recarrier (AST.recarrier (Pre.Binder.apply body (.inr ())) (Sum.map first id))
          (Sum.elim id (λ _ => receipt))) fuel = _ at hBody
        rw [recarrierComp, Sum.elim_comp_map, Function.id_comp, Function.comp_id] at hBody
        obtain ⟨bodyFuel, hTarget⟩ := ih
          (base := ⟨base.UId ⊕ Unit⟩) (trm := Pre.Binder.apply body (.inr ()))
          (first := Sum.elim first (λ _ => receipt))
          (second := Sum.elim second (λ _ => receipt))
          (by
            intro carrier inferred sourceFuel hSource
            cases carrier with
            | inl outer => exact hReplace outer inferred sourceFuel hSource
            | inr slot => exact ⟨sourceFuel, hSource⟩) hBody
        exact ⟨bodyFuel + 1, by
          rw [recarrierFn, infer.eq_3, ← inputEqual]
          change (infer (AST.recarrier (AST.recarrier (Pre.Binder.apply body (.inr ())) (Sum.map second id))
            (Sum.elim id (λ _ => receipt))) bodyFuel).map _ = _
          rw [recarrierComp, Sum.elim_comp_map, Function.id_comp, Function.comp_id, hTarget]
          rfl⟩
    | ref carrier under =>
      exact hReplace (mapRef under carrier) typ (fuel + 1) hInfer
    | apply fn arg =>
      change infer (.apply (AST.recarrier fn first) (AST.recarrier arg first)) (fuel + 1) = _ at hInfer
      obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih hReplace hArg
      have hFnMore := Monotone.termInfer (AST.recarrier fn second) fnFuel (max fnFuel argFuel) _
        (Nat.le_max_left _ _) hFnTarget
      have hArgMore := Monotone.termInfer (AST.recarrier arg second) argFuel (max fnFuel argFuel) _
        (Nat.le_max_right _ _) hArgTarget
      exact ⟨max fnFuel argFuel + 1, by
        change infer (.apply (AST.recarrier fn second) (AST.recarrier arg second)) _ = _
        simp only [infer.eq_4, hFnMore, hArgMore]
        exact congrArg Rec.Outcome.yield (ite_eq_left (rfl : input = input))⟩

omit build in
private theorem runtimeReplace {source target : Root} {trm : source.Trm}
    {first : source.UId → refs.UId ⊕ Unit} {second : target.UId → refs.UId ⊕ Unit}
    (map : source.UId → target.UId)
    (hReplace : ∀ receipt, runtimeRefs refs first (.ref receipt .same) →
      runtimeRefs refs second (.ref (map receipt) .same))
    (runtime : runtimeRefs refs first trm) : runtimeRefs refs second (AST.recarrier trm map) := by
  induction runtime generalizing target with
  | lit => exact .lit
  | @fn base origins annotation body runtime ih =>
    rw [recarrierFn]
    apply runtimeRefs.fn
    apply ih (Sum.map map id)
    intro carrier runtime
    cases carrier with
    | inl outer =>
      have original : runtimeRefs refs origins (.ref outer .same) := by
        cases runtime <;> solve_by_elim [runtimeRefs.bound, runtimeRefs.value]
      cases hReplace outer original <;> solve_by_elim [runtimeRefs.bound, runtimeRefs.value]
    | inr slot => exact .bound rfl
  | apply fn arg ihFn ihArg => exact .apply (ihFn map hReplace) (ihArg map hReplace)
  | bound bound => exact hReplace _ (.bound bound)
  | value origin lookup runtime ih => exact hReplace _ (.value origin lookup runtime)

private theorem mintedValueInfer (value : refs.base.Val) {fuel : Nat} {typ : refs.base.Typ}
    (hInfer : infer value.asTrm fuel = .yield (some typ)) :
    infer (.ref (build.uid2val value).val .same) (fuel + 1) =
      .yield (some typ) := by
  simp only [infer.eq_5, mapRef, (build.uid2val value).property]
  exact hInfer

private theorem inferEvalSafety (trm : refs.base.Trm) (inferFuel : Nat) (typ : refs.base.Typ)
    (runtime : runtimeRefs refs Sum.inl trm)
    (hInfer : infer trm inferFuel = .yield (some typ)) :
    (eval trm).isSemiDecidable (λ result =>
      ∃ valueFuel, infer result.asTrm valueFuel = .yield (some typ) ∧
        runtimeRefs refs Sum.inl result.asTrm) := by
  intro evalFuel
  induction evalFuel generalizing trm inferFuel typ with
  | zero => trivial
  | succ evalFuel ih =>
    cases inferFuel with
    | zero => simp [infer] at hInfer
    | succ inferFuel =>
      cases trm with
      | val value => exact ⟨inferFuel + 1, hInfer, runtime⟩
      | ref carrier under =>
        cases runtime <;> simp_all [infer.eq_5, eval.eq_4]
        exact ⟨inferFuel, hInfer⟩
      | apply fn arg =>
        cases runtime
        rename_i runtimeFn runtimeArg
        obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
        have hFnSafety := ih fn inferFuel (.TFn input typ) runtimeFn hFn
        have hArgSafety := ih arg inferFuel input runtimeArg hArg
        cases hFnEval : eval fn evalFuel <;> try cases ‹Option refs.base.Val›
        all_goals simp [hFnEval] at hFnSafety
        case outOfFuel =>
          cases eval arg evalFuel <;> simp [eval.eq_3, hFnEval]
        case yield.some fnValue =>
          obtain ⟨⟨fnInferFuel, hFnValue⟩, runtimeFnValue⟩ := hFnSafety
          cases fnInferFuel <;> (try cases fnValue) <;> simp [Root.Val.asTrm, infer.eq_1, infer.eq_2] at hFnValue
          case succ.lit => cases Option.some.inj hFnValue
          case succ.fn fnInferFuel annotation body =>
            cases hArgEval : eval arg evalFuel <;> try cases ‹Option refs.base.Val›
            all_goals simp [hArgEval] at hArgSafety
            case outOfFuel => simp [eval.eq_3, hFnEval, hArgEval]
            case yield.some argValue =>
              obtain ⟨⟨argInferFuel, hArgValue⟩, runtimeArgValue⟩ := hArgSafety
              obtain ⟨fnOutput, hBody, hFnType⟩ := inferFnSuccess hFnValue
              rcases Pre.AST.TFn.inj hFnType with ⟨rfl, rfl⟩
              let receipt := (build.uid2val argValue).val
              obtain ⟨bodyFuel, hBodyTarget⟩ := inferReplace
                (second := Sum.elim id (λ _ => receipt))
                (by
                  intro carrier inferred sourceFuel hSource
                  cases carrier with
                  | inl outer => exact ⟨sourceFuel, hSource⟩
                  | inr slot =>
                    cases sourceFuel <;> simp [infer, mapRef, Sum.elim] at hSource
                    cases hSource
                    exact ⟨argInferFuel + 1, mintedValueInfer argValue hArgValue⟩) hBody
              have hRuntimeBody : runtimeRefs refs Sum.inl (Binder.apply body receipt) := by
                cases runtimeFnValue with
                | fn runtimeBody =>
                  apply runtimeReplace (Sum.elim id (λ _ => receipt)) ?_ runtimeBody
                  intro carrier runtime
                  cases carrier with
                  | inl outer =>
                    cases runtime <;> solve_by_elim [runtimeRefs.value]
                  | inr slot =>
                    exact .value rfl (build.uid2val argValue).property runtimeArgValue
              simpa only [eval.eq_3, hFnEval, hArgEval] using
                ih (Binder.apply body receipt) bodyFuel _ hRuntimeBody hBodyTarget

/-- Successful runtime inference excludes evaluation rejection and preserves the result's type. -/
theorem main (trm : refs.base.Trm) (fuel : Nat) (typ : refs.base.Typ)
    (runtime : runtimeRefs refs Sum.inl trm)
    (hInfer : trm.infer fuel = .yield (some typ)) : safety trm typ := by
  intro evalFuel
  have safe := inferEvalSafety trm fuel typ runtime hInfer evalFuel
  rcases result : eval trm evalFuel with (_ | value) | _
  all_goals simp only [result, Bool.false_eq_true] at safe ⊢
  obtain ⟨valueFuel, typed, _⟩ := safe
  exact ⟨valueFuel, by rw [typed]⟩

end

end Fundamental

end Lp2lc.Active.STLC
