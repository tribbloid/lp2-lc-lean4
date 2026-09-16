import «Lp2lc».Active.STLC.STLCDef

/-
Warning: this is for runtime test, DO NOT use it in any proof!
-/

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

mutual
  /-- Structural equality over [AST], passing the receipt/data comparators down to subterms. -/
  def astBEq {P : Parameters} {l : Label} (a b : AST P l)
      (beqC : P.C → P.C → Bool) (beqD : P.D → P.D → Bool) : Bool :=
    match a, b with
    | .primitive, .primitive => true
    | .fn a1 a2, .fn b1 b2 => astBEq a1 b1 beqC beqD && astBEq a2 b2 beqC beqD
    | .lit a, .lit b => beqD a b
    | .lam a1 a2, .lam b1 b2 => binderBEq a1 b1 beqC beqD && astBEq a2 b2 beqC beqD
    | .val a, .val b => astBEq a b beqC beqD
    | .apply a1 a2, .apply b1 b2 => astBEq a1 b1 beqC beqD && astBEq a2 b2 beqC beqD
    | .ref a, .ref b => beqC a b
    | _, _ => false

  /-- Structural equality over [Binder], rebuilding the receipt comparator for the shifted slot. -/
  def binderBEq {P : Parameters} {l : Label} (a b : Binder P l)
      (beqC : P.C → P.C → Bool) (beqD : P.D → P.D → Bool) : Bool :=
    match a, b with
    | .mk a, .mk b =>
      astBEq a b
        (λ x y =>
          match x, y with
          | .inl a, .inl b => beqC a b
          | .inr (), .inr () => true
          | _, _ => false)
        beqD
end

mutual
  /-- Structural hash over [AST], passing the receipt/data hashers down to subterms. -/
  def astHash {P : Parameters} {l : Label} (self : AST P l)
      (hashC : P.C → UInt64) (hashD : P.D → UInt64) : UInt64 :=
    match self with
    | .primitive => 1
    | .fn tIn tOut => mixHash 2 (mixHash (astHash tIn hashC hashD) (astHash tOut hashC hashD))
    | .lit repr => mixHash 3 (hashD repr)
    | .lam body tIn => mixHash 4 (mixHash (binderHash body hashC hashD) (astHash tIn hashC hashD))
    | .val v => mixHash 5 (astHash v hashC hashD)
    | .apply fnTerm arg => mixHash 6 (mixHash (astHash fnTerm hashC hashD) (astHash arg hashC hashD))
    | .ref receipt => mixHash 7 (hashC receipt)

  /-- Structural hash over [Binder], rebuilding the receipt hasher for the shifted slot. -/
  def binderHash {P : Parameters} {l : Label} (self : Binder P l)
      (hashC : P.C → UInt64) (hashD : P.D → UInt64) : UInt64 :=
    match self with
    | .mk body =>
      astHash body
        (λ receipt =>
          match receipt with
          | .inl outer => hashC outer
          | .inr () => 8)
        hashD
end

/-- Content hash of the mixed value-or-type payload carried by an indexed AST. -/
def hashSum {P : Parameters} (payload : AST.Val P ⊕ AST.Typ P)
    (hashC : P.C → UInt64) (hashD : P.D → UInt64) : UInt64 :=
  match payload with
  | .inl v => astHash v hashC hashD
  | .inr t => astHash t hashC hashD

end Lp2lc.Active.STLC
