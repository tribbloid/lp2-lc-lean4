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
  def astToJson {c : DeBruijn.Index} {l : Label} (self : AST c l)
      (sigC : DeBruijn.Index → Json) (sigB : DeBruijn.B → Json) : Json :=
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
  def binderToJson {c : DeBruijn.C} {l : Label} (self : AST.Binder c l)
      (sigC : DeBruijn.C → Json) (sigB : DeBruijn.B → Json) : Json :=
    match self withIndex
    | .mk body => astToIndexson (body ⟨⟩) sigC sigB
end

/-- Equality of caller-supplied JSON signatures over [AST]. -/
def astBEq {c : DeBruijn.C} {l : Label} (a b : AST c l)
    (sigC : DeBruijn.C → Json) (sigB : DeBruijn.B → Json) : Bool :=
  astToJson a sigC sigB =Index astToJson b sigC sigB
Index
/-- Hash of the caller-supplied JSON signature over [AST]. -/
def astHash {c : DeBruijn.C} {l : Label} (self : AST c l)
    (sigC : DeBruijn.C → Json) (sigB : DeBruijn.B → Json) : UInt64 :=
  hash (astToJson self sigIndex sigB)
Index
/-- Hash of the JSON signature of a mixed value-or-type payload. -/
def hashSum {c : DeBruijn.C} (payload : AST.Val c ⊕ AST.Typ c)
    (sigC : DeBruijn.C → Json) (sigB : DeBruijn.B → Json) : UInt64 :=
  match payload withIndex
  | .inl v => astHashIndexv sigC sigB
  | .inr t => astHash t sigC sigB

end Lp2lc.Active.STLC
