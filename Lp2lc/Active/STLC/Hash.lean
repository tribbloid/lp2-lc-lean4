import Lean.Data.Json
import «Lp2lc».Active.STLC.STLCDef

/-
Warning: this is for runtime test, DO NOT use it in any proof!
-/

namespace Lp2lc.Active.STLC

open Lean (Json)
open Lp2lc.Active.Util

private structure RefIndex (P : Parameters) where
  level : Nat
  read : P.TRef → Nat
  lift (T : URef) (level : Nat) (read : T → Nat) : P.TRefInc T → Nat
  fresh (T : URef) : P.TRefInc T

private def RefIndex.next {P : Parameters} (self : RefIndex P) : RefIndex P.Next :=
  { level := self.level + 1
    read := self.lift P.TRef self.level self.read
    lift := self.lift
    fresh := self.fresh }

private def deBruijnRefs (c : Nat) : RefIndex (AST.At c) :=
  { level := c
    read := AST.refIndex c
    lift := λ _ level read carrier => carrier.elim read (λ _ => level + 1)
    fresh := λ _ => .inr .only }

mutual
  /--
  Canonical JSON signature of an [AST]: a single tree traversal that both
  signature equality and hashing delegate to. Reference indices and bytecode values are
  injected through caller-supplied signature functions, so wildcard or
  content-based comparators are expressed by their canonical image.
  -/
  private def astToJsonAux {P : Parameters} {l : Label} (self : AST P l)
      (refs : RefIndex P) (sigC : Nat → Json) (sigB : P.B → Json) : Json :=
    match self with
    | .TLit => "primitive"
    | .TFn tIn tOut =>
      .arr #["fn", astToJsonAux tIn refs sigC sigB, astToJsonAux tOut refs sigC sigB]
    | .lit repr => .arr #["lit", sigB repr]
    | .fn tIn body =>
      .arr #["lam", binderToJsonAux body refs sigC sigB, astToJsonAux tIn refs sigC sigB]
    | .val v => .arr #["val", astToJsonAux v refs sigC sigB]
    | .apply fnTerm arg =>
      .arr #["apply", astToJsonAux fnTerm refs sigC sigB, astToJsonAux arg refs sigC sigB]
    | .ref carrier => .arr #["ref", sigC (refs.read carrier)]

  /-- Canonical JSON signature of a [Binder], applying its body to the new slot. -/
  private def binderToJsonAux {P : Parameters} {l : Label} (self : AST.Binder P l)
      (refs : RefIndex P) (sigC : Nat → Json) (sigB : P.B → Json) : Json :=
    match self with
    | .mk body => astToJsonAux (body (refs.fresh P.TRef)) refs.next sigC sigB
end

/-- JSON signature of concrete De Bruijn syntax. -/
def astToJson {c : Nat} {l : Label} (self : AST (AST.At c) l)
    (sigC : Nat → Json) (sigB : String → Json) : Json :=
  astToJsonAux self (deBruijnRefs c) sigC sigB

/-- Equality of caller-supplied JSON signatures over [AST]. -/
def astBEq {c : Nat} {l : Label} (a b : AST (AST.At c) l)
    (sigC : Nat → Json) (sigB : String → Json) : Bool :=
  astToJson a sigC sigB == astToJson b sigC sigB

/-- Hash of the caller-supplied JSON signature over [AST]. -/
def astHash {c : Nat} {l : Label} (self : AST (AST.At c) l)
    (sigC : Nat → Json) (sigB : String → Json) : UInt64 :=
  hash (astToJson self sigC sigB)

/-- Hash of the JSON signature of a mixed value-or-type payload. -/
def hashSum {c : Nat} (payload : AST.Val (AST.At c) ⊕ AST.Typ (AST.At c))
    (sigC : Nat → Json) (sigB : String → Json) : UInt64 :=
  match payload with
  | .inl v => astHash v sigC sigB
  | .inr t => astHash t sigC sigB

end Lp2lc.Active.STLC
