import Lean.Data.Json
import «Lp2lc».Active.DSub.Serial.Def

/-!
Runtime syntax signatures for tests; do not use signature equality in proofs.
Primitive callbacks are opaque and represented only by their declared result type.
-/

namespace Lp2lc.Active.DSub

open Lean (Json)

@[match_pattern] private abbrev bind := @Pre.Binder.mk

private def visit {P l} (self : Pre.AST P l) (get : ∀ index, P.I.getTRef index)
    (sig : P.I.Index ⊕ P.B → Json) : Json :=
  match self with
  | .TTop => "top"
  | .TBot => "bottom"
  | .TLit => "primitive"
  | .TFn tIn (bind output) =>
    .arr #["fn", visit tIn get sig, visit (output (get P.Next.index)) get sig]
  | .lit repr => .arr #["lit", sig (.inr repr)]
  | .fn tIn (bind body) =>
    .arr #["lam", visit (body (get P.Next.index)) get sig, visit tIn get sig]
  | .fnPrimitive (bind output) _ => .arr #["primitiveFn", visit (output (get P.Next.index)) get sig]
  | .TMember lower upper => .arr #["member", visit lower get sig, visit upper get sig]
  | .TSel value => .arr #["select", visit value get sig]
  | .typeDef typ => .arr #["typeDef", visit typ get sig]
  | .ref _ under => .arr #["ref", sig (.inl under.sourceIndex)]
  | .val value => .arr #["val", visit value get sig]
  | .apply fnTerm arg =>
    .arr #["apply", visit fnTerm get sig, visit arg get sig]

variable {n m : Nat} {l : Label}

/-- JSON signature of serial syntax, opening each dependent binder at its next context. -/
def astToJson (self : AST n l) (sigC : Nat → Json) (sigB : String → Json) : Json :=
  visit self (λ _ => .only) (Sum.elim (sigC ∘ ULift.down) sigB)

/-- Equality of caller-supplied signatures, with independently signed reference contexts. -/
def astBEq (a : AST n l) (b : AST m l)
    (sigC : Nat → Json) (sigB : String → Json) (otherSigC : Nat → Json := sigC) : Bool :=
  astToJson a sigC sigB == astToJson b otherSigC sigB

/-- Hash of the same JSON signature used by `astBEq`. -/
def astHash (self : AST n l) (sigC : Nat → Json) (sigB : String → Json) : UInt64 :=
  hash (astToJson self sigC sigB)

/-- Hash of a mixed value-or-type payload's syntax signature. -/
def hashSum (payload : Val n ⊕ Typ n) (sigC : Nat → Json) (sigB : String → Json) : UInt64 :=
  match payload with
  | .inl value => astHash value sigC sigB
  | .inr typ => astHash typ sigC sigB

end Lp2lc.Active.DSub
