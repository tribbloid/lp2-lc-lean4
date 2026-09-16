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

#guard vFalse.infer.shouldYieldsBool 1 .primitive

#guard vTrue.infer.shouldYieldsBool 1 .primitive

#guard primitiveIdFn.infer.shouldYieldsBool 2 (.fn .primitive .primitive)

#guard primitiveIdFnOnFalse.infer.shouldYieldsBool 3 .primitive

#guard get1st.infer.shouldYieldsBool 3 (.fn .primitive (.fn .primitive .primitive))

#guard get2nd.infer.shouldYieldsBool 3 (.fn .primitive (.fn .primitive .primitive))

#guard get1stOnTuple.infer.shouldYieldsBool 5 .primitive

#guard get2ndOnTuple.infer.shouldYieldsBool 5 .primitive

#guard primitiveTrueFn.infer.shouldYieldsBool 2 (.fn .primitive .primitive)

#guard primitiveTrueFnOnFalse.infer.shouldYieldsBool 3 .primitive

#guard TypeHinted.hintedFalse.infer.shouldYieldsBool 1 .primitive

#guard TypeHinted.hintedIdFn.infer.shouldYieldsBool 2 (.fn .primitive .primitive)

#guard TypeHinted.hintedIdFnOnFalse.infer.shouldYieldsBool 3 .primitive

#guard FreeCapture.directRef.infer.shouldYieldsBool 2 .primitive

#guard (AST.ref ((inferInstance : BuildEnv refs).uid2typCtx.inv (.primitive : Typ)).val : Trm).infer.shouldYieldsBool 1 .primitive

#guard Malformed.applyIdFnOnItself.infer.shouldFailBool 3

#guard Malformed.idFnOnFalse2.infer.shouldFailBool 4

#guard Malformed.apply1.infer.shouldFailBool 4

#guard Malformed.primitiveApply.infer.shouldFailBool 2

end infer

end Trm

end Sanity
