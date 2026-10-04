import Lean.Data.Json
import «Lp2lc».Active.STLC.STLCDef

/-
Warning: this is for runtime test, DO NOT use it in any proof!
-/

namespace Lp2lc.Active.STLC

open Lean (Json)
open Lp2lc.Active.Util

/--
Canonical JSON signature of syntax: a single tree traversal that both
signature equality and hashing delegate to. Reference indices and bytecode values are
injected through caller-supplied signature functions, so wildcard or
content-based comparators are expressed by their canonical image.
-/
private def visit {P : Parameters} {l} (self : Pre.AST P l)
    (get : (index : P.I.Index) → P.I.getTRef index)
    (sigC : P.I.Index → Json) (sigB : P.B → Json) : Json :=
  match self with
  | .TLit => "primitive"
  | .TFn tIn tOut =>
    .arr #["fn", visit tIn get sigC sigB, visit tOut get sigC sigB]
  | .lit repr => .arr #["lit", sigB repr]
  | .fn tIn (.mk body) =>
    .arr #["lam", visit (body (get P.Next.Next.index)) get sigC sigB, visit tIn get sigC sigB]
  | .val v => .arr #["val", visit v get sigC sigB]
  | .apply fnTerm arg =>
    .arr #["apply", visit fnTerm get sigC sigB, visit arg get sigC sigB]
  | .ref _ under => .arr #["ref", sigC under.sourceIndex]

/-- JSON signature of concrete serial syntax. -/
def astToJson {n l} (self : AST n l)
    (sigC : Nat → Json) (sigB : String → Json) : Json :=
  visit self (λ _ => .only) sigC sigB

/-- Equality of caller-supplied JSON signatures over [AST]. -/
def astBEq {n l} (a b : AST n l)
    (sigC : Nat → Json) (sigB : String → Json) : Bool :=
  astToJson a sigC sigB == astToJson b sigC sigB

/-- Hash of the caller-supplied JSON signature over [AST]. -/
def astHash {n l} (self : AST n l)
    (sigC : Nat → Json) (sigB : String → Json) : UInt64 :=
  hash (astToJson self sigC sigB)

/-- Hash of the JSON signature of a mixed value-or-type payload. -/
def hashSum {n} (payload : Val n ⊕ Typ n)
    (sigC : Nat → Json) (sigB : String → Json) : UInt64 :=
  match payload with
  | .inl v => astHash v sigC sigB
  | .inr t => astHash t sigC sigB

end Lp2lc.Active.STLC
