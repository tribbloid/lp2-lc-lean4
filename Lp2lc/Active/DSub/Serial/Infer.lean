import «Lp2lc».Active.DSub.Serial.Infra

namespace Lp2lc.Active.DSub.CompilerTyp

open Lp2lc.Active.Util

mutual

private def scopeBound (self : CompilerTyp) : Nat :=
  match self with
  | ⟨n, _, captured⟩ => max n (bindingsBound captured)
termination_by sizeOf self

private def bindingsBound (self : NatBindings CompilerTyp) : Nat :=
  match self with
  | .empty => 0
  | .set entries index typ => max index (max (scopeBound typ) (bindingsBound entries))
termination_by sizeOf self

end

private def pathAlias (index : Nat) : CompilerTyp :=
  let path : Typ index := .TSel (.ref (IndexEncoding.SerialProxy.only (C := index)) .same)
  ⟨index, .TMember path path, .empty⟩

/-- Combine fuel-bounded checks, retaining a conclusive conjunction or disjunction. -/
private def combine (shortCircuit : Bool) (left right : Rec.Outcome Bool) : Rec.Outcome Bool :=
  match left, right with
  | .yield left, .yield right => .yield (if shortCircuit then left || right else left && right)
  | .yield value, _ => if value == shortCircuit then .yield value else .outOfFuel
  | _, .yield value => if value == shortCircuit then .yield value else .outOfFuel
  | _, _ => .outOfFuel

mutual

private def memberBounds (self : CompilerTyp) (context : NatBindings CompilerTyp) :
    RecOpt (CompilerTyp × CompilerTyp) := λ fuel =>
  match fuel, self.value with
  | 0, _ => .outOfFuel
  | _ + 1, .TMember lower upper =>
    .yield (some (⟨self.n, lower, self.captured⟩, ⟨self.n, upper, self.captured⟩))
  | _ + 1, .TBot =>
    .yield (some (⟨self.n, .TTop, self.captured⟩, ⟨self.n, .TBot, self.captured⟩))
  | fuel + 1, .TSel value =>
    (selectionBounds value self.captured context fuel).flatMap (λ result =>
      match result with
      | some (_, upper) => memberBounds upper context fuel
      | none => .yield none)
  | _ + 1, _ => .yield none

private def selectionBounds {n} (value : Val n) (captured context : NatBindings CompilerTyp) :
    RecOpt (CompilerTyp × CompilerTyp) := λ fuel =>
  match fuel, value with
  | 0, _ => .outOfFuel
  | _ + 1, .typeDef typ => .yield (some (⟨n, typ, captured⟩, ⟨n, typ, captured⟩))
  | fuel + 1, .ref _ under =>
    match (captured under.sourceIndex.down).orElse (λ _ => context under.sourceIndex.down) with
    | some typ => memberBounds typ context fuel
    | none => .yield none
  | _ + 1, _ => .yield none

end

/-- Fuel-bounded structural subtyping; false reports nonacceptance, without a completeness claim. -/
def subtype (self upper : CompilerTyp) (context : NatBindings CompilerTyp := .empty) : Rec Bool := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self.value, upper.value with
    | .TBot, _ => .yield true
    | _, .TTop => .yield true
    | .TLit, .TLit => .yield true
    | .TMember lower₁ upper₁, .TMember lower₂ upper₂ =>
      combine false
        (subtype ⟨upper.n, lower₂, upper.captured⟩ ⟨self.n, lower₁, self.captured⟩ context fuel)
        (subtype ⟨self.n, upper₁, self.captured⟩ ⟨upper.n, upper₂, upper.captured⟩ context fuel)
    | .TFn input₁ output₁, .TFn input₂ output₂ =>
      let rightInput : CompilerTyp := ⟨upper.n, input₂, upper.captured⟩
      let fresh := max (scopeBound self) (max (scopeBound upper) (bindingsBound context)) + 1
      let alias := pathAlias fresh
      combine false
        (subtype rightInput ⟨self.n, input₁, self.captured⟩ context fuel)
        (subtype ⟨self.n + 1, output₁.apply .only, self.captured.set (self.n + 1) alias⟩
          ⟨upper.n + 1, output₂.apply .only, upper.captured.set (upper.n + 1) alias⟩
          (context.set fresh rightInput) fuel)
    | _, _ =>
      let samePath :=
        match self.value, upper.value with
        | .TSel (.ref _ left), .TSel (.ref _ right) =>
          (self.captured left.sourceIndex.down).isNone &&
            (upper.captured right.sourceIndex.down).isNone &&
            left.sourceIndex.down == right.sourceIndex.down
        | _, _ => false
      if samePath then .yield true else
        let follow (selected other : CompilerTyp) (widen : Bool) :=
          match selected.value with
          | .TSel value =>
            (selectionBounds value selected.captured context fuel).flatMap (λ result =>
              match result with
              | some (lower, upper) =>
                if widen then subtype upper other context fuel else subtype other lower context fuel
              | none => .yield false)
          | _ => .yield false
        combine true (follow self upper true) (follow upper self false)

namespace Monotone

private theorem combine {left right left' right' : Rec.Outcome Bool} {result : Bool}
    (shortCircuit : Bool)
    (hLeft : ∀ value, left = .yield value → left' = .yield value)
    (hRight : ∀ value, right = .yield value → right' = .yield value)
    (h : CompilerTyp.combine shortCircuit left right = .yield result) :
    CompilerTyp.combine shortCircuit left' right' = .yield result := by
  cases left <;> cases right <;> cases shortCircuit <;> simp_all [CompilerTyp.combine]
  all_goals split at h <;> simp_all
  all_goals cases left' <;> cases right' <;> simp_all

private theorem bounds (less more : Nat) (hFuel : less ≤ more) :
    (∀ self context result, memberBounds self context less = .yield result →
      memberBounds self context more = .yield result) ∧
    (∀ {n} (value : Val n) captured context result, selectionBounds value captured context less = .yield result →
      selectionBounds value captured context more = .yield result) := by
  induction less generalizing more with
  | zero => constructor <;> intros <;> contradiction
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      obtain ⟨hMember, hSelection⟩ := ih more (Nat.le_of_succ_le_succ hFuel)
      constructor
      · rintro ⟨n, typ, captured⟩ context result h
        cases typ
        all_goals simp only [memberBounds, Rec.Outcome.flatMap] at h ⊢
        all_goals repeat split at h
        all_goals simp_all <;> subst_vars <;> rfl
      · intro n value captured context result h
        cases value
        all_goals simp only [selectionBounds] at h ⊢
        all_goals repeat split at h
        all_goals simp_all

/-- Completed subtype checks retain their result when fuel increases. -/
theorem subtype (self upper : CompilerTyp) (context : NatBindings CompilerTyp) :
    (self.subtype upper context).Monotone := by
  intro less more result hFuel h
  induction less generalizing self upper context more result with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      replace hFuel := Nat.le_of_succ_le_succ hFuel
      obtain ⟨_, hSelection⟩ := bounds fuel more hFuel
      simp only [CompilerTyp.subtype.eq_2] at h ⊢
      repeat' (split at h <;> try simp_all only [Bool.false_eq_true, ite_true, ite_false])
      all_goals apply combine _ ?_ ?_ h
      all_goals intro value hBranch
      all_goals try exact ih _ _ _ more value hFuel hBranch
      all_goals try simp only [Rec.Outcome.flatMap] at hBranch ⊢
      all_goals repeat split at hBranch
      all_goals simp_all [-Bool.forall_bool]

end Monotone

end Lp2lc.Active.DSub.CompilerTyp

namespace Lp2lc.Active.DSub.AST

open Lp2lc.Active.Util
open CompilerTyp (pathAlias)

private def andThen {T R : Type 2} (result : Rec.Outcome (Option T))
    (next : (value : T) → Rec.Outcome (Option R)) : Rec.Outcome (Option R) :=
  result.flatMap (λ value =>
    match value with
    | some value => next value
    | none => .yield none)

private def reference (context index : Nat) : Option (Val context) :=
  match context with
  | 0 =>
    if index = 0 then some (.ref (IndexEncoding.SerialProxy.only (C := 0)) .same) else none
  | n + 1 =>
    if index = n + 1 then some (.ref (IndexEncoding.SerialProxy.only (C := n + 1)) .same) else
      match reference n index with
      | some (.ref carrier under) => some (.ref carrier (.lower under))
      | _ => none

private def capturePaths (bindings : NatBindings CompilerTyp) : NatBindings CompilerTyp :=
  match bindings with
  | .empty => .empty
  | .set entries index _ => (capturePaths entries).set index (pathAlias index)

/-- Re-express a type in the caller's context without evaluating terms.
An abstract member path stays stable; eliminating a captured path requires equivalent member bounds. -/
private def quoteType (self : CompilerTyp) (imports : Option ExeBindings)
    (context : NatBindings CompilerTyp) (target : Nat) (names : Nat → Nat)
    (targetCaptures : NatBindings CompilerTyp) : RecOpt (Typ target) := λ fuel =>
  match fuel, self.value with
  | 0, _ => .outOfFuel
  | _ + 1, .TTop => .yield (some .TTop)
  | _ + 1, .TBot => .yield (some .TBot)
  | _ + 1, .TLit => .yield (some .TLit)
  | fuel + 1, .TMember lower upper =>
    andThen (quoteType ⟨self.n, lower, self.captured⟩ imports context target names targetCaptures fuel) (λ lower =>
      (quoteType ⟨self.n, upper, self.captured⟩ imports context target names targetCaptures fuel).map
        (Option.map (.TMember lower)))
  | fuel + 1, .TFn input output =>
    andThen (quoteType ⟨self.n, input, self.captured⟩ imports context target names targetCaptures fuel) (λ input =>
      let fresh := max target (max (CompilerTyp.scopeBound self)
        (max (CompilerTyp.bindingsBound context) (CompilerTyp.bindingsBound targetCaptures))) + 1
      let alias := pathAlias fresh
      (quoteType ⟨self.n + 1, output.apply .only, self.captured.set (self.n + 1) alias⟩ imports
        (context.set fresh ⟨target, input, targetCaptures⟩) (target + 1)
        (λ index => if index = fresh then target + 1 else names index)
        (targetCaptures.set (target + 1) alias) fuel).map (Option.map (λ output => .TFn input (.mk (λ _ => output)))))
  | fuel + 1, .TSel (.typeDef typ) =>
    quoteType ⟨self.n, typ, self.captured⟩ imports context target names targetCaptures fuel
  | fuel + 1, .TSel (.ref _ under) =>
    let index := under.sourceIndex.down
    match self.captured index with
    | some typ =>
      andThen (CompilerTyp.memberBounds typ context fuel) (λ (lower, upper) =>
        (CompilerTyp.combine false (lower.subtype upper context fuel) (upper.subtype lower context fuel)).flatMap
          (λ accepted => if accepted then quoteType upper none context target names targetCaptures fuel
            else .yield none))
    | none =>
      match imports with
      | some bindings =>
        match bindings index with
        | some value => quoteType ⟨value.n, .TSel value.value, .empty⟩ (some value.captured)
            context target names targetCaptures fuel
        | none => .yield none
      | none =>
        match context index with
        | some typ => andThen (CompilerTyp.memberBounds typ context fuel) (λ _ =>
            .yield ((reference target (names index)).map .TSel))
        | none => .yield none
  | _ + 1, .TSel _ => .yield none

/-- Resolve annotations using runtime imports and the current hypothetical type bindings. -/
private def resolveType {n} (self : Typ n) (bindings : CompilerBindings) : RecOpt (Typ n) :=
  quoteType ⟨n, self, capturePaths bindings.types⟩ (some bindings.runtime) bindings.types n id .empty

private def functionType (self : CompilerTyp) (context : NatBindings CompilerTyp) :
    RecOpt (Σ n, Typ n × Binder n .typ × NatBindings CompilerTyp) := λ fuel =>
  match fuel, self.value with
  | 0, _ => .outOfFuel
  | _ + 1, .TFn input output => .yield (some ⟨self.n, input, output, self.captured⟩)
  | _ + 1, .TBot => .yield (some ⟨self.n, .TTop, .mk (λ _ => .TBot), self.captured⟩)
  | fuel + 1, .TSel value =>
    andThen (CompilerTyp.selectionBounds value self.captured context fuel) (λ (_, upper) =>
      functionType upper context fuel)
  | _ + 1, _ => .yield none

/-- Infer from runtime imports and hypothetical types, retaining dependent stable paths.
Primitive result annotations are inferred here; their implementations require validation at evaluation. -/
def infer {n} (self : Trm n) (bindings : CompilerBindings := .empty) : RecOpt CompilerTyp := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | _ + 1, .val (.lit _) => .yield (some ⟨n, .TLit, .empty⟩)
  | fuel + 1, .val (.typeDef typ) =>
    (resolveType typ bindings fuel).map (Option.map (λ typ => ⟨n, .TMember typ typ, .empty⟩))
  | fuel + 1, .val (.fn input body) =>
    andThen (resolveType input bindings fuel) (λ input =>
      let entries := bindings.set (n + 1) ⟨n, input, .empty⟩
      andThen (infer (body.apply .only) entries fuel) (λ output =>
        (quoteType output none entries.types (n + 1) id .empty fuel).map
          (Option.map (λ output => ⟨n, .TFn input (.mk (λ _ => output)), .empty⟩))))
  | fuel + 1, .val (.fnPrimitive output _) =>
    (resolveType (output.apply .only) (bindings.set (n + 1) ⟨n, .TLit, .empty⟩) fuel).map
      (Option.map (λ output => ⟨n, .TFn .TLit (.mk (λ _ => output)), .empty⟩))
  | fuel + 1, .val (.ref _ under) =>
    let found :=
      match bindings under.sourceIndex.down with
      | some (.inl typ) => .yield (some typ)
      | some (.inr value) => infer value.value.asTrm value.captured fuel
      | none => .yield none
    andThen found (λ typ =>
      (quoteType typ none bindings.types n id .empty fuel).map (Option.map (λ typ => ⟨n, typ, .empty⟩)))
  | fuel + 1, .apply fn arg =>
    andThen (infer fn bindings fuel) (λ fnType =>
      andThen (infer arg bindings fuel) (λ argType =>
        andThen (functionType fnType bindings.types fuel) (λ ⟨index, input, output, captured⟩ =>
          (argType.subtype ⟨index, input, captured⟩ bindings.types fuel).flatMap (λ accepted =>
            if accepted then
              let replacement :=
                match arg with
                | .val (.ref _ under) =>
                  if (bindings.types under.sourceIndex.down).isSome then pathAlias under.sourceIndex.down else argType
                | _ => argType
              (quoteType ⟨index + 1, output.apply .only, captured.set (index + 1) replacement⟩ none
                bindings.types n id .empty fuel).map (Option.map (λ typ => ⟨n, typ, .empty⟩))
            else .yield none))))

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ : CompilerTyp) : Prop :=
  self.infer bindings fuel = .yield (some typ)

namespace Monotone

/-- Completed quotation results retain their syntax when fuel increases. -/
private theorem quoteType (self : CompilerTyp) (imports : Option ExeBindings)
    (context : NatBindings CompilerTyp) (target : Nat) (names : Nat → Nat)
    (targetCaptures : NatBindings CompilerTyp) :
    (AST.quoteType self imports context target names targetCaptures).Monotone := by
  intro less more result hFuel h
  induction less generalizing self imports context target names targetCaptures more result with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      replace hFuel := Nat.le_of_succ_le_succ hFuel
      obtain ⟨hMember, _⟩ := CompilerTyp.Monotone.bounds fuel more hFuel
      have hSubtype (self upper : CompilerTyp) (context : NatBindings CompilerTyp) (value : Bool) :=
        CompilerTyp.Monotone.subtype self upper context fuel more value hFuel
      have hCheck (lower upper : CompilerTyp) (context : NatBindings CompilerTyp) (value : Bool) :=
        CompilerTyp.Monotone.combine (result := value) false (hSubtype lower upper context) (hSubtype upper lower context)
      rcases self with ⟨n, typ, captured⟩
      cases typ
      all_goals try cases ‹Val n›
      all_goals simp only [AST.quoteType, andThen, Rec.Outcome.map, Rec.Outcome.flatMap] at h ⊢
      all_goals repeat' split at h
      all_goals try simp_all [-Bool.forall_bool]
      all_goals first | exact ih _ _ _ _ _ _ more _ hFuel h | subst_vars; rfl

private theorem functionType (self : CompilerTyp) (context : NatBindings CompilerTyp) :
    (AST.functionType self context).Monotone := by
  intro less more result hFuel h
  induction less generalizing self context more result with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      replace hFuel := Nat.le_of_succ_le_succ hFuel
      obtain ⟨_, hSelection⟩ := CompilerTyp.Monotone.bounds fuel more hFuel
      rcases self with ⟨n, typ, captured⟩
      cases typ
      all_goals simp only [AST.functionType, andThen, Rec.Outcome.flatMap] at h ⊢
      all_goals repeat' split at h
      all_goals simp_all <;> subst_vars <;> rfl

/-- Every completed inference result, including rejection, is preserved when fuel increases. -/
theorem termInfer {n} (trm : Trm n) (bindings : CompilerBindings) :
    (infer trm bindings).Monotone := by
  intro less more result hFuel h
  induction less generalizing n trm bindings more result with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      replace hFuel := Nat.le_of_succ_le_succ hFuel
      have hQuote (self imports context target names captures result) :=
        quoteType self imports context target names captures fuel more result hFuel
      have hFunction (self context result) := functionType self context fuel more result hFuel
      have hSubtype (self upper context result) := CompilerTyp.Monotone.subtype self upper context fuel more result hFuel
      cases trm <;> try cases ‹Val n›
      all_goals simp only [infer, resolveType, andThen, Rec.Outcome.flatMap, Rec.Outcome.map] at h ⊢
      all_goals repeat' split at h
      all_goals try simp_all [-Bool.forall_bool]
      all_goals repeat' (split at * <;> try simp_all [-Bool.forall_bool])
      all_goals subst_vars <;> first | contradiction | rfl

end Monotone

end Lp2lc.Active.DSub.AST
