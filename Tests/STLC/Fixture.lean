import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.Hash
import «Lp2lc».Active.STLC.__Infer

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

/-- Compares two string literals without relying on the reducibility of the fixture's `D`. -/
def litEq (repr expected : String) : Bool := repr == expected

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

/- FIXME: this class can have a concrete, opaque implementation, which index each AST by its hash

once the implementation is ready, all the assertion in `TrmSpec` can be replaced by a single line of #guard
-/

/-- Supplies the shared reference view and runtime value context used by STLC tests. -/
class TestEnv where
  trm2either : UIdRefs (λ C =>
    let P : Parameters := { C := C, D := String }
    AST.Val P ⊕ AST.Typ P)
  trm2valExe : {v : trm2either.Lesser _ // v.upcastV.toFun = Sum.inl}
  trm2valExeCtx : KVEquiv trm2valExe.val.toKVRefs
  trm2typExe : {v : trm2either.Lesser _ // v.upcastV.toFun = Sum.inr}
  trm2typExeCtx : KVEquiv trm2typExe.val.toKVRefs

variable [testEnv : TestEnv]

@[reducible] instance refs : HasUId2Any :=
  { D := String, uid2any := testEnv.trm2either }

/-- Compile-time typing context derived from the fixture's mixed reference view. -/
instance build : BuildEnv refs where
  uid2typ := testEnv.trm2typExe.val
  uid2typCtx := testEnv.trm2typExeCtx

/-- Structural equality on the fixture's values; opaque receipts are always considered equal. -/
instance : BEq (AST.Val refs.Parameters) :=
  ⟨λ a b => astBEq a b (λ _ _ => true) litEq⟩

/-- Structural equality on the fixture's types. -/
instance : BEq (AST.Typ refs.Parameters) :=
  ⟨λ a b => astBEq a b (λ _ _ => true) litEq⟩

@[simp]
theorem trm2valLookup
    (receipt : {uid // testEnv.trm2valExe.val.ev uid}) :
    refs.uid2any.get receipt.val = .inl (testEnv.trm2valExe.val.get receipt) :=
  (testEnv.trm2valExe.val.equivariance receipt).symm.trans
    (congrFun testEnv.trm2valExe.property _)

/- Concrete, opaque [TestEnv] implementation whose receipts are content hashes. -/
namespace Fixture

/-- The structural content hash of an indexed AST. -/
abbrev TestHash := UInt64

/--
The receipt carrier: a content hash paired with a boxed AST payload.

The hash is the index, while the boxed payload makes the otherwise-noninvertible
hash losslessly recoverable without relying on mutable storage.
-/
abbrev TestUId := TestHash × Unit

/-- The fixed STLC parameters shared by the concrete fixture. -/
abbrev TestParameters : Parameters := { C := TestUId, D := String }

/-- Boxes a `Type 2` payload into a `Type` value so it can be stored in a receipt. -/
unsafe def boxPayload (payload : AST.Val TestParameters ⊕ AST.Typ TestParameters) : Unit :=
  unsafeCast payload

/-- Recovers a boxed payload; unsafe and only meaningful for values produced by [boxPayload]. -/
unsafe def unboxPayload (box : Unit) : AST.Val TestParameters ⊕ AST.Typ TestParameters :=
  unsafeCast box

set_option warn.classDefReducibility false in
/-- The concrete fixture: receipts carry their content hash and a boxed payload. -/
unsafe def _testEnvImpl : TestEnv :=
  let trm2either : UIdRefs (λ C =>
      let P : Parameters := { C := C, D := String }
      AST.Val P ⊕ AST.Typ P) :=
    {
      UId := TestUId
      get := λ receipt => unboxPayload receipt.2
    }
  let trm2valExe : {v : trm2either.Lesser _ // v.upcastV.toFun = Sum.inl} :=
    ⟨{
        ev := λ _ => True
        get := λ receipt =>
          match unboxPayload receipt.val.2 with
          | .inl value => value
          | .inr _ => unsafeCast ()
        upcastV := ⟨Sum.inl, by
          intro a b h
          cases h
          rfl⟩
        equivariance := unsafeCast True.intro
      }, rfl⟩
  let trm2valExeCtx : KVEquiv trm2valExe.val.toKVRefs :=
    {
      inv := λ value => ⟨(hashSum (.inl value) (λ receipt => receipt.1) (λ repr => hash repr), boxPayload (.inl value)), True.intro⟩
      rightInv := unsafeCast True.intro
      leftInv := unsafeCast True.intro
    }
  let trm2typExe : {v : trm2either.Lesser _ // v.upcastV.toFun = Sum.inr} :=
    ⟨{
        ev := λ _ => True
        get := λ receipt =>
          match unboxPayload receipt.val.2 with
          | .inr typ => typ
          | .inl _ => unsafeCast ()
        upcastV := ⟨Sum.inr, by
          intro a b h
          cases h
          rfl⟩
        equivariance := unsafeCast True.intro
      }, rfl⟩
  let trm2typExeCtx : KVEquiv trm2typExe.val.toKVRefs :=
    {
      inv := λ typ => ⟨(hashSum (.inr typ) (λ receipt => receipt.1) (λ repr => hash repr), boxPayload (.inr typ)), True.intro⟩
      rightInv := unsafeCast True.intro
      leftInv := unsafeCast True.intro
    }
  { trm2either := trm2either, trm2valExe := trm2valExe, trm2valExeCtx := trm2valExeCtx,
    trm2typExe := trm2typExe, trm2typExeCtx := trm2typExeCtx }

/-- The concrete [TestEnv] instance: an opaque fixture indexed by AST hash. -/
@[instance, implemented_by _testEnvImpl] axiom hashTestEnv : TestEnv

end Fixture

end Tests.STLC.Sanity
