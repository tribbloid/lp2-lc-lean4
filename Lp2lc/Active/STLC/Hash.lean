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

private def jsonPair (tag : Json) (left right : Rec.Outcome Json) : Rec.Outcome Json :=
  left.flatMap (λ left => right.map (λ right => .arr #[tag, left, right]))

section variable {refs : URef} [numbering : SlotNumbering refs] {l : Label}

  /--
  Canonical JSON signature of an [AST]: a single tree traversal that both
  signature equality and hashing delegate to. Reference indices and bytecode values are
  injected through caller-supplied signature functions, so wildcard or
  content-based comparators are expressed by their canonical image.
  -/
  private def astToJsonAux {refs} [numbering : SlotNumbering refs] {l} (self : AST 0 l refs)
      (sigC : Nat → Json) (sigB : String → Json) : Rec Json := λ fuel =>
    match fuel, self with
    | 0, _ => .outOfFuel
    | _, .TLit => .yield "primitive"
    | fuel + 1, .TFn tIn tOut =>
      jsonPair "fn" (astToJsonAux tIn sigC sigB fuel) (astToJsonAux tOut sigC sigB fuel)
    | _, .lit repr => .yield (.arr #["lit", sigB repr])
    -- Canonical JSON signature of a [Binder], applying its body to the new slot.
    | fuel + 1, .fn tIn (.mk body) =>
      jsonPair "lam" (astToJsonAux (body (.inr .only)) sigC sigB fuel) (astToJsonAux tIn sigC sigB fuel)
    | fuel + 1, .val v => (astToJsonAux v sigC sigB fuel).map (λ value => .arr #["val", value])
    | fuel + 1, .apply fnTerm arg =>
      jsonPair "apply" (astToJsonAux fnTerm sigC sigB fuel) (astToJsonAux arg sigC sigB fuel)
    | _, .ref carrier under =>
      .yield (.arr #["ref", sigC (numbering.read (under.shift (λ _ => .inl) carrier))])

/-- JSON signature of concrete De Bruijn syntax, reporting insufficient traversal fuel. -/
def astToJson (self : AST 0 l refs) (sigC : Nat → Json) (sigB : String → Json) : Rec Json :=
  astToJsonAux self sigC sigB

/-- Equality of caller-supplied JSON signatures over [AST]. -/
def astBEq (a b : AST 0 l refs) (sigC : Nat → Json) (sigB : String → Json) : Rec Bool := λ fuel =>
  (astToJson a sigC sigB fuel).flatMap (λ left => (astToJson b sigC sigB fuel).map (left == ·))

/-- Hash of the caller-supplied JSON signature over [AST]. -/
def astHash (self : AST 0 l refs) (sigC : Nat → Json) (sigB : String → Json) : Rec UInt64 := λ fuel =>
  (astToJson self sigC sigB fuel).map hash

/-- Hash of the JSON signature of a mixed value-or-type payload. -/
def hashSum (payload : AST 0 .val refs ⊕ AST 0 .typ refs)
    (sigC : Nat → Json) (sigB : String → Json) : Rec UInt64 :=
  match payload with
  | .inl v => astHash v sigC sigB
  | .inr t => astHash t sigC sigB

end

end Lp2lc.Active.STLC
