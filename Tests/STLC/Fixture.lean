import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC


/-
FIXME: this class can have a concrete, opaque implementation, which index each AST by its hash

once the implementation is ready, all the assertion in `TrmSpec` can be replaced by a single line of #guard
-/

/-- Supplies the shared reference view and runtime value context used by STLC tests. -/
class TestEnv where
  trm2either : UIdRefs (λ C =>
    let P : Parameters := { C := C, D := String }
    AST.Val P ⊕ AST.Typ P)
  trm2valExe : {v : trm2either.Lesser _ // v.upcastV.toFun = Sum.inl}
  trm2valExeCtx : KVEquiv trm2valExe.val.toKVRefs

variable [testEnv : TestEnv]

@[reducible] instance refs : HasUId2Any :=
  { D := String, uid2any := testEnv.trm2either }

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
  { trm2either := trm2either, trm2valExe := trm2valExe, trm2valExeCtx := trm2valExeCtx }

/-- The concrete [TestEnv] instance: an opaque fixture indexed by AST hash. -/
@[instance, implemented_by _testEnvImpl] axiom hashTestEnv : TestEnv

end Fixture

end Tests.STLC.Sanity
