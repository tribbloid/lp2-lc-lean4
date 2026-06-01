import «Tests».DTLC.ValDemo

namespace Tests.DTLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Trm

def false {I : Index} : AST.Trm I :=
  .val (.primitive "false")

def true {I : Index} : AST.Trm I :=
  .val (.primitive "true")

def idFn {I : Index} : AST.Trm I :=
  .val (.fn (fun x => .ref x))

def idFnOnFalse {I : Index} : AST.Trm I :=
  .apply idFn false

def get1st {I : Index} : AST.Trm I :=
  .val
    (.fn (fun x =>
      .val
        (.fn (fun _y => .ref x))))

def get2nd {I : Index} : AST.Trm I :=
  .val
    (.fn (fun _x =>
      .val
        (.fn (fun y => .ref y))))

def get1stOnTuple {I : Index} : AST.Trm I :=
  .apply
    (.apply get1st false)
    true

def get2ndOnTuple {I : Index} : AST.Trm I :=
  .apply
    (.apply get2nd false)
    true

def apply1stOn2ndFn {I : Index} : AST.Trm I :=
  .val (.fn (fun f =>
      .val (.fn (fun x =>
        .apply
          (.ref f)
          (.ref x)))))

def apply1stOn2ndFnOnTuple {I : Index} : AST.Trm I :=
  .apply
    (.apply apply1stOn2ndFn idFn)
    false

def applyidFnOnItself {I : Index} : AST.Trm I :=
  .apply idFn idFn

def idFnOnFalse2 {I : Index} : AST.Trm I :=
  .apply applyidFnOnItself false

def malformedPrimitiveApply {I : Index} : AST.Trm I :=
  .apply false true

def malformedApply1 {I : Index} : AST.Trm I :=
  .apply
    (.apply idFn false)
    true

def annotatedFalse {I : Index} : AST.Trm I :=
  .val (.primitive "false") (some .primitive)

def annotatedIdFn {I : Index} : AST.Trm I :=
  .val
    (.fn
      (fun x => .ref x (some .primitive)))
    (some (.depFn .primitive (fun _x => .primitive)))

def annotatedIdFnOnFalse {I : Index} : AST.Trm I :=
  .apply annotatedIdFn annotatedFalse (some .primitive)

end Trm

end Sanity
