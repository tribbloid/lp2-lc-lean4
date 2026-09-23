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

#guard vFalse.infer.shouldYieldsBool 1 .TLit

#guard vTrue.infer.shouldYieldsBool 1 .TLit

#guard primitiveIdFn.infer.shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard primitiveIdFnOnFalse.infer.shouldYieldsBool 3 .TLit

#guard get1st.infer.shouldYieldsBool 3 (.TFn .TLit (.TFn .TLit .TLit))

#guard get2nd.infer.shouldYieldsBool 3 (.TFn .TLit (.TFn .TLit .TLit))

#guard get1stOnTuple.infer.shouldYieldsBool 5 .TLit

#guard get2ndOnTuple.infer.shouldYieldsBool 5 .TLit

#guard primitiveTrueFn.infer.shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard primitiveTrueFnOnFalse.infer.shouldYieldsBool 3 .TLit

#guard TypeHinted.hintedFalse.infer.shouldYieldsBool 1 .TLit

#guard TypeHinted.hintedIdFn.infer.shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard TypeHinted.hintedIdFnOnFalse.infer.shouldYieldsBool 3 .TLit

#guard FreeCapture.directRef.infer.shouldYieldsBool 2 .TLit

#guard (AST.ref ((inferInstance : BuildEnv refs).uid2typCtx.inv (.TLit : Typ)) : AST.Trm refs.Parameters).infer.shouldYieldsBool 1 .TLit

#guard Malformed.applyIdFnOnItself.infer.shouldFailBool 3

#guard Malformed.idFnOnFalse2.infer.shouldFailBool 4

#guard Malformed.apply1.infer.shouldFailBool 4

#guard Malformed.primitiveApply.infer.shouldFailBool 2

end infer

end Trm

end Sanity
