import Lean.Data.Json
import «Lp2lc».Active.STLC.Serial.Def

/-
Warning: this is for runtime test, DO NOT use it in any proof!
-/

namespace Lp2lc.Active.STLC

open Lean (Json)

-- File-private structural view; the caller supplies its encoding's sole context proxy.
@[match_pattern] private abbrev bind := @Pre.Binder.mk

section
variable (sigOp : ∀ {P}, (P.B → Pre.AST P .val) → Json)

/--
Canonical JSON signature of syntax: a single tree traversal that both
signature equality and hashing delegate to. Reference indices and bytecode values are
injected through caller-supplied signature functions, so wildcard or
content-based comparators are expressed by their canonical image.
Primitive callbacks are opaque: `sigOp` supplies their signatures, defaulting to a wildcard.
Signature equality does not establish callback equality.
-/
private def visit {P l} (self : Pre.AST P l) (get : ∀ index, P.I.getTRef index)
    (sig : P.I.Index ⊕ P.B → Json) : Json :=
  match self with
  | .TLit => "primitive"
  | .TFn tIn tOut =>
    .arr #["fn", visit tIn get sig, visit tOut get sig]
  | .lit repr => .arr #["lit", sig (.inr repr)]
  | .fn tIn (bind body) =>
    .arr #["lam", visit (body (get P.Next.index)) get sig, visit tIn get sig]
  | .fnPrimitive tOut op => .arr #["primitiveFn", visit tOut get sig, sigOp op]
  | .val v => .arr #["val", visit v get sig]
  | .apply fnTerm arg =>
    .arr #["apply", visit fnTerm get sig, visit arg get sig]
  | .ref _ under => .arr #["ref", sig (.inl under.sourceIndex)]

end

/-- JSON signature of concrete serial syntax. -/
def astToJson {n l} (self : AST n l)
    (sigC : Nat → Json) (sigB : String → Json)
    (sigOp : ∀ {P}, (P.B → Pre.AST P .val) → Json := λ _ => .null) : Json :=
  visit sigOp self (λ _ => .only) (Sum.elim (sigC ∘ ULift.down) sigB)

/-- Equality of caller-supplied JSON signatures over [AST]. -/
def astBEq {n l} (a b : AST n l)
    (sigC : Nat → Json) (sigB : String → Json)
    (sigOp : ∀ {P}, (P.B → Pre.AST P .val) → Json := λ _ => .null) : Bool :=
  astToJson a sigC sigB sigOp == astToJson b sigC sigB sigOp

/-- Hash of the caller-supplied JSON signature over [AST]. -/
def astHash {n l} (self : AST n l)
    (sigC : Nat → Json) (sigB : String → Json)
    (sigOp : ∀ {P}, (P.B → Pre.AST P .val) → Json := λ _ => .null) : UInt64 :=
  hash (astToJson self sigC sigB sigOp)

/-- Hash of the JSON signature of a mixed value-or-type payload. -/
def hashSum {n} (payload : Val n ⊕ Typ n)
    (sigC : Nat → Json) (sigB : String → Json)
    (sigOp : ∀ {P}, (P.B → Pre.AST P .val) → Json := λ _ => .null) : UInt64 :=
  match payload with
  | .inl v => astHash v sigC sigB sigOp
  | .inr t => astHash t sigC sigB sigOp

end Lp2lc.Active.STLC
