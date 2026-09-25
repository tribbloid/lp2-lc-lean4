import Lean.Data.Json
import «Lp2lc».Active.STLC.STLCDef

/-
Warning: this is for runtime test, DO NOT use it in any proof!
-/

namespace Lp2lc.Active.STLC

open Lean (Json)
open Lp2lc.Active.Util

mutual
  /--
  Canonical JSON signature of an [AST]: a single tree traversal that both
  signature equality and hashing delegate to. The receipt/bytecode carriers are
  injected through caller-supplied signature functions, so wildcard or
  content-based comparators are expressed by their canonical image.
  -/
  def astToJson {P : Parameters} {c : P.C} {l : Label} (self : AST c l)
      (sigC : P.C → Json) (sigB : P.B → Json) : Json :=
    match self with
    | .TLit => "primitive"
    | .TFn tIn tOut =>
      .arr #["fn", astToJson tIn sigC sigB, astToJson tOut sigC sigB]
    | .lit repr => .arr #["lit", sigB repr]
    | .fn tIn body =>
      .arr #["lam", binderToJson body sigC sigB, astToJson tIn sigC sigB]
    | .val v => .arr #["val", astToJson v sigC sigB]
    | .apply fnTerm arg =>
      .arr #["apply", astToJson fnTerm sigC sigB, astToJson arg sigC sigB]
    | .ref (c := receipt) _ _ => .arr #["ref", sigC receipt]

  /-- Canonical JSON signature of a [Binder], applying its body to the unique proxy. -/
  def binderToJson {P : Parameters} {c : P.C} {l : Label} (self : Binder c l)
      (sigC : P.C → Json) (sigB : P.B → Json) : Json :=
    match self with
    | .mk body => astToJson (body ⟨⟩) sigC sigB
end

/-- Equality of caller-supplied JSON signatures over [AST]. -/
def astBEq {P : Parameters} {c : P.C} {l : Label} (a b : AST c l)
    (sigC : P.C → Json) (sigB : P.B → Json) : Bool :=
  astToJson a sigC sigB == astToJson b sigC sigB

/-- Hash of the caller-supplied JSON signature over [AST]. -/
def astHash {P : Parameters} {c : P.C} {l : Label} (self : AST c l)
    (sigC : P.C → Json) (sigB : P.B → Json) : UInt64 :=
  hash (astToJson self sigC sigB)

/-- Hash of the JSON signature of a mixed value-or-type payload. -/
def hashSum {P : Parameters} {c : P.C} (payload : AST.Val c ⊕ AST.Typ c)
    (sigC : P.C → Json) (sigB : P.B → Json) : UInt64 :=
  match payload with
  | .inl v => astHash v sigC sigB
  | .inr t => astHash t sigC sigB

end Lp2lc.Active.STLC
