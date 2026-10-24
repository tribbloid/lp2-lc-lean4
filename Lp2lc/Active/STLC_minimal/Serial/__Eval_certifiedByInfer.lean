import «Lp2lc».Active.STLC_minimal.Serial.Infer

namespace Lp2lc.Active.STLC_minimal.AST

open Lp2lc.Active.Util

namespace CertifiedByInfer

/-- A returned value certified at the caller's independently inferred type. -/
abbrev CertifiedVal (typ : Typ) :=
  {value : ExeVal // (value.value.asTrm.infer value.captured).isDecidable (· = typ)}

/-- Certified evaluation preserves runtime corruption and may exhaust its fuel. -/
abbrev Result (typ : Typ) := Rec (Return (CertifiedVal typ))

variable {n fuel : Nat} {typ : Typ} {entries : CompilerBindings}

private def preservesType (source target : RecOpt Typ) : Prop :=
  ∀ {fuel typ}, source fuel = .yield (some typ) → ∃ targetFuel, target targetFuel = .yield (some typ)

private theorem inferApplySuccess {fn arg : Trm n}
    (hInfer : infer (.apply fn arg) entries (fuel + 1) = .yield (some typ)) :
    ∃ input, infer fn entries fuel = .yield (some (.TFn input typ)) ∧
      infer arg entries fuel = .yield (some input) := by
  simp only [infer.eq_5] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals injection hInfer; subst_vars; exact ⟨_, rfl, rfl⟩

private theorem inferFnSuccess {annotation : Typ n} {body : Binder n .trm}
    (hInfer : infer (.val (.fn annotation body)) entries (fuel + 1) = .yield (some typ)) :
    let input := resolveType annotation
    ∃ output, infer (body.apply .only)
        (entries.set (n + 1) ⟨n, annotation, .empty⟩) fuel = .yield (some output) ∧
      typ = .TFn input output := by
  cases hBody : infer (body.apply .only)
      (entries.set (n + 1) ⟨n, annotation, .empty⟩) fuel <;>
    (try cases ‹Option Typ›) <;> simp_all [infer.eq_3, Rec.Outcome.map, Option.map]
  exact ⟨_, rfl, (Option.some.inj hInfer).symm⟩

-- Certification uses inference monotonicity and establishes the remaining inference facts locally.
private def entryFits (entry : Option (CompilerTyp ⊕ ExeVal)) (typ : Typ) : Prop :=
  ∃ fuel,
    (match entry with
    | some (.inr ⟨_, value, captured⟩) => infer value.asTrm captured fuel
    | some (.inl ⟨_, input, _⟩) => .yield (some (resolveType input))
    | none => .yield none) = .yield (some typ)

/-- Replacing hypothetical entries by inferable runtime values preserves inference. -/
private theorem inferReplace {trm : Trm n} {source target : CompilerBindings}
    (hReplace : ∀ index typ, entryFits (source index) typ → entryFits (target index) typ) :
    preservesType (infer trm source) (infer trm target) := by
  intro fuel typ hInfer
  induction fuel generalizing n trm source target typ with
  | zero => cases hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => exact ⟨1, by simpa only [infer.eq_2] using hInfer⟩
      | fn annotation body =>
        obtain ⟨output, hBody, rfl⟩ := inferFnSuccess hInfer
        obtain ⟨bodyFuel, hTarget⟩ := ih (target := target.set (n + 1) ⟨n, annotation, .empty⟩)
          (by
            intro index inputTyp
            simp only [CompilerBindings.get, NatBindings.get]
            split <;> first | exact id | exact hReplace index inputTyp) hBody
        exact ⟨bodyFuel + 1, by simp only [infer.eq_3, hTarget, Rec.Outcome.map]; rfl⟩
      | fnPrimitive _ _ => exact ⟨fuel + 1, by simpa only [infer.eq_6] using hInfer⟩
    | ref carrier under =>
      obtain ⟨targetFuel, hTarget⟩ := hReplace under.sourceIndex.down typ
        ⟨fuel, by
          simp only [infer.eq_4] at hInfer
          split at hInfer <;> simp_all⟩
      exact ⟨targetFuel + 1, by
        simp only [infer.eq_4]
        split <;> simp_all [entryFits]⟩
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih hReplace hArg
      exact ⟨max fnFuel argFuel + 1, by
        rw [infer.eq_5,
          Monotone.termInfer fn target fnFuel (max fnFuel argFuel) _ (Nat.le_max_left _ _) hFnTarget,
          Monotone.termInfer arg target argFuel (max fnFuel argFuel) _ (Nat.le_max_right _ _) hArgTarget]
        exact congrArg _ (ite_eq_left (rfl : input = input))⟩

/-- Each returned value preserves every successful inference of its source term. -/
private def evalInternal {n} (self : Trm n) (bindings : ExeBindings) :
    Rec (Return {value : ExeVal //
      preservesType (self.infer bindings) (value.value.asTrm.infer value.captured)}) := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | fuel + 1, .val value => .yield (.some ⟨.mk n value bindings, λ {inferFuel typ} hInfer => ⟨inferFuel, hInfer⟩⟩)
  | fuel + 1, .ref _ under =>
    match hBinding : bindings under.sourceIndex.down with
    | none => .outOfFuel
    | some (.mk context value captured) => .yield (.some ⟨.mk context value captured, by
        rintro (_ | inferFuel) typ hInfer
        · cases hInfer
        · simp only [infer, infer.eq_4, CompilerBindings.get, hBinding, Option.map] at hInfer
          exact ⟨inferFuel, hInfer⟩⟩)
  | fuel + 1, .apply fn arg =>
    match evalInternal fn bindings fuel, evalInternal arg bindings fuel with
    | .yield (.some ⟨.mk context (.fn annotation body) captured, fnSafe⟩), .yield (.some argResult) =>
      let bodyBindings := captured.set (context + 1) argResult.val
      have bodyTyped : preservesType (infer (.apply fn arg) bindings)
          (infer (body.apply .only) bodyBindings) := by
        rintro (_ | inferFuel) typ hInfer
        · cases hInfer
        · obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
          obtain ⟨_ | fnFuel, hFnValue⟩ := fnSafe hFn
          · cases hFnValue
          · obtain ⟨output, hBody, hFnType⟩ := inferFnSuccess hFnValue
            rcases Pre.AST.TFn.inj hFnType with ⟨rfl, rfl⟩
            rcases argResult with ⟨⟨argContext, argValue, argCaptured⟩, argSafe⟩
            have argTyped := argSafe hArg
            exact inferReplace (target := bodyBindings)
              (by
                intro index inputTyp hSource
                simp only [bodyBindings, CompilerBindings.get, NatBindings.get] at hSource ⊢
                split at hSource <;> simp_all [entryFits, Option.map]) hBody
      (evalInternal (body.apply .only) bodyBindings fuel).map (·.map (λ bodyResult =>
        ⟨bodyResult.val, λ hInfer => (bodyTyped hInfer).elim (λ _ => bodyResult.property)⟩))
    | .yield (.some ⟨.mk context (.fnPrimitive tOut op) captured, fnSafe⟩),
        .yield (.some ⟨.mk _ (.lit repr) _, _⟩) =>
      letI : DecidableEq Typ := λ a b => typDecidableLE a b
      match hCheck : infer (.val (op repr)) captured fuel with
      | .yield (some checked) =>
        if hSame : checked = resolveType tOut then
          .yield (.some ⟨.mk context (op repr) captured, by
            rintro (_ | inferFuel) typ hInfer
            · cases hInfer
            · obtain ⟨input, hFn, _⟩ := inferApplySuccess hInfer
              obtain ⟨fnFuel, hFnValue⟩ := fnSafe hFn
              cases fnFuel with
              | zero => cases hFnValue
              | succ fnFuel =>
                simp only [Val.asTrm, infer.eq_6] at hFnValue
                cases hFnValue
                exact ⟨fuel, by rw [hSame] at hCheck; exact hCheck⟩⟩)
        else .yield .corrupted
      | .yield none => .yield .corrupted
      | .outOfFuel => .outOfFuel
    | .yield .corrupted, .yield _
    | .yield _, .yield .corrupted => .yield .corrupted
    | _, _ => .outOfFuel

end CertifiedByInfer

open CertifiedByInfer

/-- Evaluate an independently inferred term and certify its returned value at the inferred type. -/
def eval_certified {n} (self : Trm n) (bindings : ExeBindings := .empty)
    {inferFuel : Nat} {typ : Typ}
    (hInfer : self.infer bindings inferFuel = .yield (some typ)) : Result typ := λ fuel =>
  (evalInternal self bindings fuel).map (·.map (λ result =>
    ⟨result.val, (result.property hInfer).imp (λ _ hValue => by rw [hValue])⟩))

end Lp2lc.Active.STLC_minimal.AST
