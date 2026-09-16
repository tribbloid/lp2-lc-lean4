import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.Hash
import «Lp2lc».Active.STLC.__Infer

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

/-- Compares two string literals without relying on the reducibility of the fixture's `D`. -/
def litEq (repr expected : String) : Bool := repr == expected

/- FIXME: this class can have a concrete, opaque implementation, which index each AST by its hash

once the implementation is ready, all the assertion in `TrmSpec` can be replaced by a single line of #guard
-/

/-- Supplies the shared reference view and runtime value context used by STLC tests. -/
class TestEnv extends HasUId where
  trm2either : KVRefs UId (
    let P : Parameters := { C := UId, D := String }
    AST.Val P ⊕ AST.Typ P)
  trm2valExe : trm2either.Lesser {_x : UId // True}
    (AST.Val { C := {_x : UId // True}, D := String })
  trm2valExeCtx : KVEquiv trm2valExe.toKVRefs
  trm2typExe : trm2either.Lesser UId (AST.Typ { C := UId, D := String })
  trm2typExeCtx : KVEquiv trm2typExe.toKVRefs

variable [testEnv : TestEnv]

@[reducible] instance refs : HasUId2Any :=
  { D := String, UId := testEnv.UId, uid2any := testEnv.trm2either }

/-- Compile-time typing context derived from the fixture's mixed reference view. -/
instance build : BuildEnv refs where
  uid2typ := testEnv.trm2typExe
  uid2typCtx := testEnv.trm2typExeCtx

/-- Structural equality on the fixture's values; opaque receipts are always considered equal. -/
instance : BEq (AST.Val refs.Parameters) :=
  ⟨λ a b => astBEq a b (λ _ _ => true) litEq⟩

/-- Structural equality on the fixture's types. -/
instance : BEq (AST.Typ refs.Parameters) :=
  ⟨λ a b => astBEq a b (λ _ _ => true) litEq⟩

@[simp]
theorem trm2valLookup
    (receipt : {_uid : testEnv.UId // True}) :
    refs.uid2any.get (testEnv.trm2valExe.upcastK receipt) =
      testEnv.trm2valExe.upcastV (testEnv.trm2valExe.get receipt) :=
  (testEnv.trm2valExe.equivariance receipt).symm

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
  let trm2either : KVRefs TestUId (AST.Val TestParameters ⊕ AST.Typ TestParameters) :=
    {
      get := λ receipt => unboxPayload receipt.2
    }
  let trm2valExe : trm2either.Lesser {x : TestUId // True}
      (AST.Val { C := {x : TestUId // True}, D := String }) :=
    {
      get := λ receipt =>
        match unboxPayload receipt.val.2 with
        | .inl value => value.recarrier (Q := { C := {x : TestUId // True}, D := String })
            (λ uid => ⟨uid, True.intro⟩) id
        | .inr _ => unsafeCast ()
      upcastK := ⟨Subtype.val, by
        intro a b h
        exact Subtype.ext h⟩
      upcastV := ⟨λ value =>
        .inl (value.recarrier (Q := TestParameters) (λ receipt => receipt.val) id),
        unsafeCast True.intro⟩
      equivariance := unsafeCast True.intro
    }
  let trm2valExeCtx : KVEquiv trm2valExe.toKVRefs :=
    {
      inv := λ value => ⟨(hashSum (.inl (value.recarrier (Q := TestParameters)
        (λ receipt => receipt.val) id)) (λ receipt => receipt.1) (λ repr => hash repr),
        boxPayload (.inl (value.recarrier (Q := TestParameters) (λ receipt => receipt.val) id))), True.intro⟩
      rightInv := unsafeCast True.intro
      leftInv := unsafeCast True.intro
    }
  let trm2typExe : trm2either.Lesser TestUId (AST.Typ TestParameters) :=
    {
      get := λ receipt =>
        match unboxPayload receipt.2 with
        | .inr typ => typ
        | .inl _ => unsafeCast ()
      upcastK := ⟨λ receipt => receipt, by
        intro a b h
        exact h⟩
      upcastV := ⟨Sum.inr, by
        intro a b h
        cases h
        rfl⟩
      equivariance := unsafeCast True.intro
    }
  let trm2typExeCtx : KVEquiv trm2typExe.toKVRefs :=
    {
      inv := λ typ =>
        (hashSum (.inr typ) (λ receipt => receipt.1) (λ repr => hash repr), boxPayload (.inr typ))
      rightInv := unsafeCast True.intro
      leftInv := unsafeCast True.intro
    }
  { UId := TestUId, trm2either := trm2either, trm2valExe := trm2valExe, trm2valExeCtx := trm2valExeCtx,
    trm2typExe := trm2typExe, trm2typExeCtx := trm2typExeCtx }

/-- The concrete [TestEnv] instance: an opaque fixture indexed by AST hash. -/
@[instance, implemented_by _testEnvImpl] axiom hashTestEnv : TestEnv

end Fixture

end Tests.STLC.Sanity
