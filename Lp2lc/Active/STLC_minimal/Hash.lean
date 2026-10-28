import Lean.Data.Json
import «Lp2lc».Active.STLC_minimal.Serial.Def

namespace Lp2lc.Active.STLC_minimal

open Lean (Json)

@[match_pattern] private abbrev bind := @Pre.Binder.mk

private def visit {P l} (self : Pre.AST P l) (get : ∀ index, P.I.getTRef index)
    (sig : P.I.Index ⊕ P.B → Json) : Json :=
  match self with
  | .TLit => "primitive"
  | .TFn tIn tOut =>
    .arr #["fn", visit tIn get sig, visit tOut get sig]
  | .lit repr => .arr #["lit", sig (.inr repr)]
  | .fn tIn (bind body) =>
    .arr #["lam", visit (body (get P.Next.index)) get sig, visit tIn get sig]
  | .fnPrimitive tOut _ => .arr #["primitiveFn", visit tOut get sig]
  | .val v => .arr #["val", visit v get sig]
  | .apply fnTerm arg =>
    .arr #["apply", visit fnTerm get sig, visit arg get sig]
  | .ref _ under => .arr #["ref", sig (.inl under.sourceIndex)]

def astToJson {n l} (self : AST n l)
    (sigC : Nat → Json) (sigB : String → Json) : Json :=
  visit self (λ _ => .only) (Sum.elim (sigC ∘ ULift.down) sigB)

def astBEq {n m l} (a : AST n l) (b : AST m l)
    (sigC : Nat → Json) (sigB : String → Json) (otherSigC : Nat → Json := sigC) : Bool :=
  astToJson a sigC sigB == astToJson b otherSigC sigB

def astHash {n l} (self : AST n l)
    (sigC : Nat → Json) (sigB : String → Json) : UInt64 :=
  hash (astToJson self sigC sigB)

def hashSum {n} (payload : Val n ⊕ Typ n)
    (sigC : Nat → Json) (sigB : String → Json) : UInt64 :=
  match payload with
  | .inl v => astHash v sigC sigB
  | .inr t => astHash t sigC sigB

end Lp2lc.Active.STLC_minimal
