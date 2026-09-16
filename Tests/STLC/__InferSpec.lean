import «Lp2lc».Active.STLC.__Infer
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section infer
variable [testEnv : TestEnv]

abbrev Typ := AST.Typ refs.Parameters

/-- The case terms live on the runtime carrier; compile-time inference reads
them through the honest carrier upcast, so no receipt can be forged. -/
abbrev atCompileTime (trm : Trm) : AST.Trm refs.Parameters :=
  trm.recarrier Subtype.val id

#guard (atCompileTime vFalse).infer.shouldYieldsBool 1 .primitive

#guard (atCompileTime vTrue).infer.shouldYieldsBool 1 .primitive

#guard (atCompileTime primitiveIdFn).infer.shouldYieldsBool 2 (.fn .primitive .primitive)

#guard (atCompileTime primitiveIdFnOnFalse).infer.shouldYieldsBool 3 .primitive

#guard (atCompileTime get1st).infer.shouldYieldsBool 3 (.fn .primitive (.fn .primitive .primitive))

#guard (atCompileTime get2nd).infer.shouldYieldsBool 3 (.fn .primitive (.fn .primitive .primitive))

#guard (atCompileTime get1stOnTuple).infer.shouldYieldsBool 5 .primitive

#guard (atCompileTime get2ndOnTuple).infer.shouldYieldsBool 5 .primitive

#guard (atCompileTime primitiveTrueFn).infer.shouldYieldsBool 2 (.fn .primitive .primitive)

#guard (atCompileTime primitiveTrueFnOnFalse).infer.shouldYieldsBool 3 .primitive

#guard (atCompileTime TypeHinted.hintedFalse).infer.shouldYieldsBool 1 .primitive

#guard (atCompileTime TypeHinted.hintedIdFn).infer.shouldYieldsBool 2 (.fn .primitive .primitive)

#guard (atCompileTime TypeHinted.hintedIdFnOnFalse).infer.shouldYieldsBool 3 .primitive

#guard (atCompileTime FreeCapture.directRef).infer.shouldYieldsBool 2 .primitive

#guard (AST.ref ((inferInstance : BuildEnv refs).uid2typCtx.inv (.primitive : Typ)).val : AST.Trm refs.Parameters).infer.shouldYieldsBool 1 .primitive

#guard (atCompileTime Malformed.applyIdFnOnItself).infer.shouldFailBool 3

#guard (atCompileTime Malformed.idFnOnFalse2).infer.shouldFailBool 4

#guard (atCompileTime Malformed.apply1).infer.shouldFailBool 4

#guard (atCompileTime Malformed.primitiveApply).infer.shouldFailBool 2

end infer

end Trm

end Sanity
