import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.Serial.Infra

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

/-- Erase the context index of an annotation without consuming typing fuel. -/
private def closeType {n} (self : Typ n) : Typ :=
  match self with
  | .TLit => .TLit
  | .TFn input output => .TFn (closeType input) (closeType output)

/-- Fuel-bounded typing with runtime values or hypothetical types.

Application quantifies over its domain; no principal type is selected.
-/
def checkInternal {n} (self : Trm n) (typ : Typ)
    (bindings : CompilerBindings := .empty) : Rec Prop := λ fuel =>
  match fuel with
  | 0 => .yield False
  | fuel + 1 =>
    .yield (match self with
      | .val (.lit _) => .TLit ≤ typ
      | .val (.fn annotation body) =>
        match typ with
        | .TLit => False
        | .TFn input output =>
          closeType annotation = input ∧
            (checkInternal (body.apply .only) output
              (bindings.set (n + 1) (.inr input)) fuel).getOrElse False
      | .ref _ under =>
        match bindings under.sourceIndex.down with
        | some (.inl (.mk _ value captured)) =>
          (checkInternal value.asTrm typ (captured.map .inl) fuel).getOrElse False
        | some (.inr bound) => bound ≤ typ
        | none => False
      | .apply fn arg =>
        ∃ input, (checkInternal fn (.TFn input typ) bindings fuel).getOrElse False ∧
          (checkInternal arg input bindings fuel).getOrElse False)

def check {n} (self : Trm n) (typ : Typ)
    (bindings : ExeBindings := .empty) : Rec Prop :=
  checkInternal self typ (bindings.map .inl)

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ: Typ) : Prop :=
  (checkInternal self typ bindings fuel).getOrElse False

end Lp2lc.Active.STLC.AST.Semantic
