import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.Hash
import «Lp2lc».Active.STLC.__Infer

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

/-- Compares two string literals without relying on the reducibility of the fixture's `D`. -/
def litEq (repr expected : String) : Bool := repr == expected

/-- Supplies the shared reference view and runtime value context used by STLC tests.

The case files write String literals, so the fixture environment must carry
`String` as its data carrier. Stated as an explicit field instead of a
hidden runtime cast, so no receipt can forge a payload of a foreign data type.
-/
class TestEnv where
  refs : HasUId2Any
  exe : ExeEnv refs
  build : BuildEnv refs
  dEq : refs.D = _root_.String

/- The case files keep the original view names. Each view now aliases the
   environment bundle's own honest component, so no receipt outside a
   context's own evidence domain can be forged. -/
/-- Compatibility view of the shared mixed reference context used by the test cases. -/
abbrev TestEnv.trm2either (self : TestEnv) := self.refs.uid2any

/-- Compatibility view of the executable value context used by the test cases. -/
abbrev TestEnv.trm2valExe (self : TestEnv) := self.exe.uid2val

/-- Compatibility view of the executable value equivalence used by the test cases. -/
abbrev TestEnv.trm2valExeCtx (self : TestEnv) := self.exe.uid2valCtx

/-- Compatibility view of the build-time type context used by the test cases. -/
abbrev TestEnv.trm2typExe (self : TestEnv) := self.build.uid2typ

/-- Compatibility view of the build-time type equivalence used by the test cases. -/
abbrev TestEnv.trm2typExeCtx (self : TestEnv) := self.build.uid2typCtx

variable [testEnv : TestEnv]

/-- The case files' shared reference view is the fixture's own mixed view. -/
@[reducible] instance refs : HasUId2Any := testEnv.refs

/-- Compile-time typing context is the fixture's own build context. -/
instance build : BuildEnv refs := testEnv.build

/-- Casts the fixture's data into the case files' String view. -/
def toRepr (repr : testEnv.refs.D) : String :=
  testEnv.dEq.rec (motive := λ d _ => d) repr

/-- Casts the case files' String literals into the fixture's data view. -/
def ofRepr (repr : String) : testEnv.refs.D :=
  testEnv.dEq.mpr repr

/-- Compares the fixture's data values through the case files' String view. -/
def dEqLitEq (a b : testEnv.refs.D) : Bool :=
  litEq (toRepr a) (toRepr b)

/-- Structural equality on the fixture's values; opaque receipts are always considered equal. -/
instance : BEq (AST.Val refs.Parameters) :=
  ⟨λ a b => astBEq a b (λ _ _ => true) dEqLitEq⟩

/-- Structural equality on the fixture's types. -/
instance : BEq (AST.Typ refs.Parameters) :=
  ⟨λ a b => astBEq a b (λ _ _ => true) dEqLitEq⟩

@[simp]
theorem trm2valLookup
    (receipt : {_uid : refs.UId // testEnv.exe.ev _uid}) :
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
  let trm2typExe : trm2either.Lesser {x : TestUId // True} (AST.Typ TestParameters) :=
    {
      get := λ receipt =>
        match unboxPayload receipt.val.2 with
        | .inr typ => typ
        | .inl _ => unsafeCast ()
      upcastK := ⟨Subtype.val, by
        intro a b h
        exact Subtype.ext h⟩
      upcastV := ⟨Sum.inr, by
        intro a b h
        cases h
        rfl⟩
      equivariance := unsafeCast True.intro
    }
  let trm2typExeCtx : KVEquiv trm2typExe.toKVRefs :=
    {
      inv := λ typ =>
        ⟨(hashSum (.inr typ) (λ receipt => receipt.1) (λ repr => hash repr), boxPayload (.inr typ)), True.intro⟩
      rightInv := unsafeCast True.intro
      leftInv := unsafeCast True.intro
    }
  let refs : HasUId2Any :=
    { D := String, UId := TestUId, uid2any := trm2either }
  let exe : ExeEnv refs :=
    { ev := λ _ => True, uid2val := trm2valExe, uid2valCtx := trm2valExeCtx }
  let build : BuildEnv refs :=
    { ev := λ _ => True, uid2typ := trm2typExe, uid2typCtx := trm2typExeCtx }
  { refs := refs, exe := exe, build := build, dEq := rfl }

/-- The concrete [TestEnv] instance: an opaque fixture indexed by AST hash. -/
@[instance, implemented_by _testEnvImpl] axiom hashTestEnv : TestEnv

end Fixture

end Tests.STLC.Sanity
