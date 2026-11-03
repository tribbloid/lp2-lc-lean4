import «Lp2lc».Active.DSub.Serial.Infra

namespace Lp2lc.Active.DSub.CompilerTyp

open Lp2lc.Active.Util

mutual

private def scopeIndex (self : CompilerTyp) : Nat :=
  match self with
  | ⟨index, _, captured⟩ => max index (bindingIndex captured)
termination_by sizeOf self

private def bindingIndex (entries : NatBindings CompilerTyp) : Nat :=
  match entries with
  | .empty => 0
  | .set previous index typ => max index (max typ.scopeIndex (bindingIndex previous))
termination_by sizeOf entries

end

/-- Fresh identities must avoid both lexical slots and recursively captured substitutions. -/
private def freshIndex (index : Nat) (captured context : NatBindings CompilerTyp) (extra : Nat) : Nat :=
  max (max index (bindingIndex captured)) (max (bindingIndex context) extra) + 1

/-- An exact member records a reference substitution without replacing it by an abstract bound. -/
private def memberAlias (index : Nat) : CompilerTyp :=
  let selected : Typ index := .TSel (.ref IndexEncoding.SerialProxy.only .same)
  ⟨index, .TMember selected selected, .empty⟩

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

private def selectionBounds {n} (value : Pure n) (captured context : NatBindings CompilerTyp) :
    RecOpt (CompilerTyp × CompilerTyp) := λ fuel =>
  match fuel, value with
  | 0, _ => .outOfFuel
  | _ + 1, .val (.typeDef typ) => .yield (some (⟨n, typ, captured⟩, ⟨n, typ, captured⟩))
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
      let fresh := freshIndex self.n self.captured context upper.scopeIndex
      let alias := memberAlias fresh
      combine false
        (subtype rightInput ⟨self.n, input₁, self.captured⟩ context fuel)
        (subtype ⟨self.n + 1, output₁.apply .only, self.captured.set (self.n + 1) alias⟩
          ⟨upper.n + 1, output₂.apply .only, upper.captured.set (upper.n + 1) alias⟩
          (context.set fresh rightInput) fuel)
    | _, _ =>
      let sameReference :=
        match self.value, upper.value with
        | .TSel (.ref _ left), .TSel (.ref _ right) =>
          (self.captured left.sourceIndex.down).isNone &&
            (upper.captured right.sourceIndex.down).isNone &&
            left.sourceIndex.down == right.sourceIndex.down && (context left.sourceIndex.down).isSome
        | _, _ => false
      if sameReference then .yield true else
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

end Lp2lc.Active.DSub.CompilerTyp

namespace Lp2lc.Active.DSub.AST

open Lp2lc.Active.Util

private def andThen {T R : Type 2} (result : Rec.Outcome (Option T))
    (next : (value : T) → Rec.Outcome (Option R)) : Rec.Outcome (Option R) :=
  result.flatMap (λ value =>
    match value with
    | some value => next value
    | none => .yield none)

/-- Reconstruct only references whose source index exists in the target lexical context. -/
private def reference (target index : Nat) : Option (Pure target) :=
  match target with
  | 0 => if index == 0 then some (.ref IndexEncoding.SerialProxy.only .same) else none
  | target + 1 =>
    if index == target + 1 then some (.ref IndexEncoding.SerialProxy.only .same) else
      match reference target index with
      | some (.ref carrier under) => some (.ref carrier (.lower under))
      | _ => none

@[match_pattern] private abbrev bind := @Pre.Binder.mk

/-- Re-express a type in the caller's context without evaluating terms.
Finite syntax traversal is structural; following captured or imported selections consumes fuel.
Binder identities are renamed together; imports and exact captured members substitute selections. -/
private def quoteType (self : CompilerTyp) (imports : Option ExeBindings)
    (context : NatBindings CompilerTyp) (target : Nat) (names : Nat → Nat)
    (targetCaptures : NatBindings CompilerTyp) : RecOpt (Typ target) := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    let follow (self : CompilerTyp) (imports : Option ExeBindings) (context : NatBindings CompilerTyp)
        (target : Nat) (names : Nat → Nat) (targetCaptures : NatBindings CompilerTyp) :=
      quoteType self imports context target names targetCaptures fuel
    let rec visit {P l} (node : Pre.AST P l) (get : ∀ index, P.I.getTRef index)
        (encoding : P.I = .Serial) (captured context : NatBindings CompilerTyp)
        (target : Nat) (names : Nat → Nat) (targetCaptures : NatBindings CompilerTyp) :
        Rec.Outcome (Option (Typ target)) :=
      match node with
      | .TTop => .yield (some .TTop)
      | .TBot => .yield (some .TBot)
      | .TLit => .yield (some .TLit)
      | .TMember lower upper =>
        andThen (visit lower get encoding captured context target names targetCaptures) (λ lower =>
          (visit upper get encoding captured context target names targetCaptures).map (Option.map (.TMember lower)))
      | .TFn input (bind output) =>
        andThen (visit input get encoding captured context target names targetCaptures) (λ input =>
          let n := (encoding ▸ P.index).down
          let fresh := CompilerTyp.freshIndex n captured context
            (max target (CompilerTyp.bindingIndex targetCaptures))
          let alias := CompilerTyp.memberAlias fresh
          (visit (output (get P.Next.index)) get encoding (captured.set (n + 1) alias)
            (context.set fresh ⟨target, input, targetCaptures⟩) (target + 1)
            (λ index => if index == fresh then target + 1 else names index)
            (targetCaptures.set (target + 1) alias)).map
              (Option.map (λ output => .TFn input (.mk (λ _ => output)))))
      | .TSel (.val (.typeDef typ)) => visit typ get encoding captured context target names targetCaptures
      | .TSel (.ref _ under) =>
        let index := (encoding ▸ under.sourceIndex).down
        match captured index with
        | some typ =>
          andThen (CompilerTyp.memberBounds typ context fuel) (λ (lower, upper) =>
            (CompilerTyp.combine false (lower.subtype upper context fuel) (upper.subtype lower context fuel)).flatMap
              (λ accepted => if accepted then follow upper none context target names targetCaptures
                else .yield none))
        | none =>
          match imports with
          | some bindings =>
            match bindings index with
            | some value => follow ⟨value.n, .TSel (.val value.value), .empty⟩ (some value.captured)
                context target names targetCaptures
            | none => .yield none
          | none =>
            match context index with
            | some typ => andThen (CompilerTyp.memberBounds typ context fuel) (λ _ =>
                .yield ((reference target (names index)).map .TSel))
            | none => .yield none
      | _ => .yield none
    visit self.value (λ _ => .only) rfl self.captured context target names targetCaptures

/-- Current hypothetical variables shadow imports without rebinding an imported closure's own slots. -/
private def captureAliases (entries : NatBindings CompilerTyp) : NatBindings CompilerTyp :=
  match entries with
  | .empty => .empty
  | .set previous index _ => (captureAliases previous).set index (CompilerTyp.memberAlias index)

/-- Resolve annotations using runtime imports and the current hypothetical type bindings. -/
private def resolveType {n} (self : Typ n) (bindings : CompilerBindings) : RecOpt (Typ n) :=
  quoteType ⟨n, self, captureAliases bindings.types⟩ (some bindings.runtime) bindings.types n id .empty

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

/-- Infer from runtime imports and hypothetical types.
Primitive result annotations are inferred here; their implementations require validation at evaluation. -/
def infer {n} (self : Trm n) (bindings : CompilerBindings := .empty) : RecOpt CompilerTyp := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .pure (.val (.lit _)) => .yield (some ⟨n, .TLit, .empty⟩)
    | .pure (.val (.typeDef typ)) =>
      (resolveType typ bindings (fuel + 1)).map (Option.map (λ typ => ⟨n, .TMember typ typ, .empty⟩))
    | .pure (.val (.fn input body)) =>
      andThen (resolveType input bindings (fuel + 1)) (λ input =>
        let entries := bindings.set (n + 1) ⟨n, input, .empty⟩
        andThen (infer (body.apply .only) entries fuel) (λ output =>
          (quoteType output none entries.types (n + 1) id .empty (fuel + 1)).map
            (Option.map (λ output => ⟨n, .TFn input (.mk (λ _ => output)), .empty⟩))))
    | .pure (.val (.fnPrimitive output _)) =>
      (resolveType (output.apply .only) (bindings.set (n + 1) ⟨n, .TLit, .empty⟩) (fuel + 1)).map
        (Option.map (λ output => ⟨n, .TFn .TLit (.mk (λ _ => output)), .empty⟩))
    | .pure (.ref _ under) =>
      let found :=
        match bindings under.sourceIndex.down with
        | some (.inl typ) => .yield (some typ)
        | some (.inr value) => infer value.value.asTrm value.captured fuel
        | none => .yield none
      andThen found (λ typ =>
        (quoteType typ none bindings.types n id .empty (fuel + 1)).map (Option.map (λ typ => ⟨n, typ, .empty⟩)))
    | .apply fn arg =>
      andThen (infer fn bindings fuel) (λ fnType =>
        andThen (infer arg bindings fuel) (λ argType =>
          andThen (functionType fnType bindings.types fuel) (λ ⟨index, input, output, captured⟩ =>
            (argType.subtype ⟨index, input, captured⟩ bindings.types fuel).flatMap (λ accepted =>
              if accepted then
                let replacement :=
                  match arg with
                  | .pure (.ref _ under) =>
                    if (bindings.types under.sourceIndex.down).isSome then
                      CompilerTyp.memberAlias under.sourceIndex.down else argType
                  | _ => argType
                (quoteType ⟨index + 1, output.apply .only, captured.set (index + 1) replacement⟩ none
                  bindings.types n id .empty (fuel + 1)).map (Option.map (λ typ => ⟨n, typ, .empty⟩))
              else .yield none))))

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ : CompilerTyp) : Prop :=
  self.infer bindings fuel = .yield (some typ)

end Lp2lc.Active.DSub.AST
