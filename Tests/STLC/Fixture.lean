import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.Hash
import «Lp2lc».Active.STLC.__Infer

namespace Tests.STLC.Sanity

open Lean (toJson)
open Lp2lc.Active.Util
open Lp2lc.Active.STLC

/-- Supplies the shared reference view and runtime value context used by STLC tests.

The case files write String literals, so the fixture environment must carry
`String` as its bytecode carrier. Stated as an explicit field instead of a
hidden runtime cast, so no receipt can forge a payload of a foreign bytecode type.
-/
class TestEnv where
  refs : HasUId2Any
  exe : ExeEnv refs
  build : BuildEnv refs
  bEq : refs.B = _root_.String

/- The case files keep the original view names. Each view now aliases the
   environment bundle's own honest component, so receipts can be minted only
   through the corresponding value or type equivalence. -/
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

/-- Implicit coercion casting the fixture's bytecode into the case files' String view. -/
instance : CoeTail (testEnv.refs.B) String :=
  ⟨λ repr => testEnv.bEq.rec (motive := λ d _ => d) repr⟩

/-- Implicit coercion casting the case files' String literals into the fixture's bytecode view. -/
instance : CoeTail String (testEnv.refs.B) :=
  ⟨testEnv.bEq.mpr⟩

/-- Signs a string literal without relying on the reducibility of the fixture's `B`. -/
def litSig (repr : String) : Lean.Json := toJson repr

/-- Structural equality on the fixture's values; opaque receipts are always considered equal. -/
instance : BEq (AST.Val refs.Parameters) :=
  ⟨λ a b => astBEq a b (λ _ => .null) (λ repr => litSig repr)⟩

/-- Structural equality on the fixture's types. -/
instance : BEq (AST.Typ refs.Parameters) :=
  ⟨λ a b => astBEq a b (λ _ => .null) (λ repr => litSig repr)⟩

@[simp]
theorem trm2valLookup
    (receipt : refs.UId) :
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
abbrev TestParameters : Parameters := { Index := TestUId, B := String }

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
  let trm2valExe : trm2either.Lesser TestUId (AST.Val TestParameters) :=
    {
      get := λ receipt =>
        match unboxPayload receipt.2 with
        | .inl value => value
        | .inr _ => unsafeCast ()
      upcastK := ⟨id, Function.injective_id⟩
      upcastV := ⟨Sum.inl, by
        intro a b h
        cases h
        rfl⟩
      equivariance := unsafeCast True.intro
    }
  let trm2valExeCtx : KVEquiv trm2valExe.toKVRefs :=
    {
      inv := λ value =>
        (hashSum (.inl value) (λ receipt => toJson receipt.1) toJson,
          boxPayload (.inl value))
      rightInv := unsafeCast True.intro
      leftInv := unsafeCast True.intro
    }
  let trm2typExe : trm2either.Lesser TestUId (AST.Typ TestParameters) :=
    {
      get := λ receipt =>
        match unboxPayload receipt.2 with
        | .inr typ => typ
        | .inl _ => unsafeCast ()
      upcastK := ⟨id, Function.injective_id⟩
      upcastV := ⟨Sum.inr, by
        intro a b h
        cases h
        rfl⟩
      equivariance := unsafeCast True.intro
    }
  let trm2typExeCtx : KVEquiv trm2typExe.toKVRefs :=
    {
      inv := λ typ =>
        (hashSum (.inr typ) (λ receipt => toJson receipt.1) toJson,
          boxPayload (.inr typ))
      rightInv := unsafeCast True.intro
      leftInv := unsafeCast True.intro
    }
  let refs : HasUId2Any :=
    { B := String, UId := TestUId, uid2any := trm2either }
  let exe : ExeEnv refs :=
    { uid2val := trm2valExe, uid2valCtx := trm2valExeCtx }
  let build : BuildEnv refs :=
    { uid2typ := trm2typExe, uid2typCtx := trm2typExeCtx }
  { refs := refs, exe := exe, build := build, bEq := rfl }

/-- The concrete [TestEnv] instance: an opaque fixture indexed by AST hash. -/
@[instance, implemented_by _testEnvImpl] axiom hashTestEnv : TestEnv

end Fixture

end Tests.STLC.Sanity
