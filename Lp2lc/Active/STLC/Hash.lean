import Lean.Data.Json
import «Lp2lc».Active.STLC.STLCDef

/-
Warning: this is for runtime test, DO NOT use it in any proof!
-/

namespace Lp2lc.Active.STLC

open Lean (Json)
open Lp2lc.Active.Util

class SlotNumbering (refs : URef) where
  level : Nat
  read : refs → Nat

instance : SlotNumbering CtxEmbedding.DeBruijn.TRef where
  level := 0
  read := λ _ => 0

instance {refs : URef} [numbering : SlotNumbering refs] :
    SlotNumbering (refs ⊕ CtxEmbedding.DeBruijn.TRefNext) where
  level := numbering.level + 1
  read := λ carrier => carrier.elim numbering.read (λ _ => numbering.level + 1)

private structure RefIndex (P : Parameters) where
  level : Nat
  read : P.TRef → Nat
  inc (T : URef) (carrier : T) : P.TRefInc T
  lift (T : URef) (level : Nat) (read : T → Nat) : P.TRefInc T → Nat
  fresh (T : URef) : P.TRefInc T

private def RefIndex.next {P : Parameters} (self : RefIndex P) : RefIndex P.Next :=
  { level := self.level + 1
    read := self.lift P.TRef self.level self.read
    inc := self.inc
    lift := self.lift
    fresh := self.fresh }

mutual
  /--
  Canonical JSON signature of an [AST]: a single tree traversal that both
  signature equality and hashing delegate to. Reference indices and bytecode values are
  injected through caller-supplied signature functions, so wildcard or
  content-based comparators are expressed by their canonical image.
  -/
  private def astToJsonAux {P : Parameters} {l : Label} (self : Syntax P l)
      (refs : RefIndex P) (sigC : Nat → Json) (sigB : P.B → Json) : Json :=
    match self with
    | .TLit => "primitive"
    | .TFn tIn tOut =>
      .arr #["fn", astToJsonAux tIn refs sigC sigB, astToJsonAux tOut refs sigC sigB]
    | .lit repr => .arr #["lit", sigB repr]
    | .fn tIn body =>
      .arr #["lam", binderToJsonAux body refs.next sigC sigB, astToJsonAux tIn refs sigC sigB]
    | .val v => .arr #["val", astToJsonAux v refs sigC sigB]
    | .apply fnTerm arg =>
      .arr #["apply", astToJsonAux fnTerm refs sigC sigB, astToJsonAux arg refs sigC sigB]
    | .ref carrier under => .arr #["ref", sigC (refs.read (under.shift refs.inc carrier))]

  /-- Canonical JSON signature of a [Binder], applying its body to the new slot. -/
  private def binderToJsonAux {P : Parameters} {l : Label} (self : Scope P l)
      (refs : RefIndex P) (sigC : Nat → Json) (sigB : P.B → Json) : Json :=
    match self with
    | .mk body => astToJsonAux (body (refs.fresh P.TRef)) refs.next sigC sigB
end

local notation "𝒫" => CtxEmbedding.DeBruijn.toParameters

/-- JSON signature of concrete De Bruijn syntax. -/
def astToJson {refs : URef} [numbering : SlotNumbering refs] {l : Label}
    (self : Syntax ((𝒫).withTRef refs) l)
    (sigC : Nat → Json) (sigB : String → Json) : Json :=
  astToJsonAux self
    { level := numbering.level
      read := numbering.read
      inc := λ _ carrier => .inl carrier
      lift := λ _ level read carrier => carrier.elim read (λ _ => level + 1)
      fresh := λ _ => .inr .only } sigC sigB

/-- Equality of caller-supplied JSON signatures over [AST]. -/
def astBEq {refs : URef} [SlotNumbering refs] {l : Label}
    (a b : Syntax ((𝒫).withTRef refs) l)
    (sigC : Nat → Json) (sigB : String → Json) : Bool :=
  astToJson a sigC sigB == astToJson b sigC sigB

/-- Hash of the caller-supplied JSON signature over [AST]. -/
def astHash {refs : URef} [SlotNumbering refs] {l : Label}
    (self : Syntax ((𝒫).withTRef refs) l)
    (sigC : Nat → Json) (sigB : String → Json) : UInt64 :=
  hash (astToJson self sigC sigB)

/-- Hash of the JSON signature of a mixed value-or-type payload. -/
def hashSum {refs : URef} [SlotNumbering refs]
    (payload : Syntax ((𝒫).withTRef refs) .val ⊕
      Syntax ((𝒫).withTRef refs) .typ)
    (sigC : Nat → Json) (sigB : String → Json) : UInt64 :=
  match payload with
  | .inl v => astHash v sigC sigB
  | .inr t => astHash t sigC sigB

end Lp2lc.Active.STLC
