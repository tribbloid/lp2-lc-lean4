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
  structural equality and hashing delegate to. The receipt/data carriers are
  injected through caller-supplied signature functions, so wildcard or
  content-based comparators are expressed by their canonical image.
  -/
  def astToJson {P : Parameters} {l : Label} (self : AST P l)
      (sigC : P.C → Json) (sigD : P.D → Json) : Json :=
    match self with
    | .primitive => "primitive"
    | .fn tIn tOut =>
      .arr #["fn", astToJson tIn sigC sigD, astToJson tOut sigC sigD]
    | .lit repr => .arr #["lit", sigD repr]
    | .lam body tIn =>
      .arr #["lam", binderToJson body sigC sigD, astToJson tIn sigC sigD]
    | .val v => .arr #["val", astToJson v sigC sigD]
    | .apply fnTerm arg =>
      .arr #["apply", astToJson fnTerm sigC sigD, astToJson arg sigC sigD]
    | .ref receipt => .arr #["ref", sigC receipt]

  /-- Canonical JSON signature of a [Binder], extending the receipt signature with the bound slot. -/
  def binderToJson {P : Parameters} {l : Label} (self : Binder P l)
      (sigC : P.C → Json) (sigD : P.D → Json) : Json :=
    match self with
    | .mk body =>
      astToJson body
        (λ receipt =>
          match receipt with
          | .inl outer => sigC outer
          | .inr () => "bound")
        sigD
end

/-- Structural equality over [AST], delegated to the canonical JSON signature. -/
def astBEq {P : Parameters} {l : Label} (a b : AST P l)
    (sigC : P.C → Json) (sigD : P.D → Json) : Bool :=
  astToJson a sigC sigD == astToJson b sigC sigD

/-- Structural hash over [AST], delegated to the canonical JSON signature. -/
def astHash {P : Parameters} {l : Label} (self : AST P l)
    (sigC : P.C → Json) (sigD : P.D → Json) : UInt64 :=
  hash (astToJson self sigC sigD)

/-- Content hash of the mixed value-or-type payload carried by an indexed AST. -/
def hashSum {P : Parameters} (payload : AST.Val P ⊕ AST.Typ P)
    (sigC : P.C → Json) (sigD : P.D → Json) : UInt64 :=
  match payload with
  | .inl v => astHash v sigC sigD
  | .inr t => astHash t sigC sigD

end Lp2lc.Active.STLC
