import «Tests».DTLC.ValSpec
import «Lp2lc».Active.DTLC.Proof

namespace Tests.DTLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.DTLC

namespace Trm

def false : TrmAST :=
  .val (.primitive "false")

def true : TrmAST :=
  .val (.primitive "true")

def idFn : TrmAST :=
  .val (.fn (body := fun x => .ref x))

def idFnOnFalse : TrmAST :=
  .apply idFn false

def get1st : TrmAST :=
  .val
    (.fn (body := fun x =>
      .val
        (.fn (body := fun _y => .ref x))))

def get2nd : TrmAST :=
  .val
    (.fn (body := fun _x =>
      .val
        (.fn (body := fun y => .ref y))))

def get1stOnTuple : TrmAST :=
  .apply
    (.apply get1st false)
    true

def get2ndOnTuple : TrmAST :=
  .apply
    (.apply get2nd false)
    true

def apply1stOn2ndFn : TrmAST :=
  .val (.fn (body := fun f =>
      .val (.fn (body := fun x =>
        .apply
          (.ref f)
          (.ref x)))))

def apply1stOn2ndFnOnTuple : TrmAST :=
  .apply
    (.apply apply1stOn2ndFn idFn)
    false

def applyidFnOnItself : TrmAST :=
  .apply idFn idFn

def idFnOnFalse2 : TrmAST :=
  .apply applyidFnOnItself false

def malformedPrimitiveApply : TrmAST :=
  .apply false true

def annotatedFalse : TrmAST :=
  .val (.primitive "false") (some .primitive)

def annotatedIdFn : TrmAST :=
  .val
    (.fn
      (body := fun x => .ref x (some .primitive))
      (tIn := some .primitive))
    (some (.depFn .primitive (fun _x => .primitive)))

def annotatedIdFnOnFalse : TrmAST :=
  .apply annotatedIdFn annotatedFalse (some .primitive)

section eraseType

example {I : Index} :
    Trm.typeEraseAll (annotatedFalse : Trm I) = (false : Trm I) := rfl

example {I : Index} :
    Trm.typeEraseAll (annotatedIdFn : Trm I) =
      .val (.fn (body := fun x => .ref x) (tIn := none)) none := rfl

example {I : Index} :
    Trm.typeEraseAll (annotatedIdFnOnFalse : Trm I) =
      .apply (Trm.typeEraseAll (annotatedIdFn : Trm I)) (false : Trm I) none := rfl

example {I : Index} :
    (Trm.typeEraseAll (annotatedIdFnOnFalse : Trm I)).TypeErased :=
  Lp2lc.Active.DTLC.Trm.eraseType_isErased I (annotatedIdFnOnFalse : Trm I)

end eraseType

section eval

unsafe inductive RuntimeRef where
| val : Val RuntimeRef -> RuntimeRef
| trm : Trm RuntimeRef -> RuntimeRef

unsafe instance : FBound RuntimeRef Val where
  fwd := RuntimeRef.val
  rev := fun ref =>
    match ref with
    | .val value => value
    | .trm _ => .primitive "invalid-ref"
  fwdRoundtrip := by
    intro value
    rfl

unsafe instance : FBound RuntimeRef Trm where
  fwd := RuntimeRef.trm
  rev := fun ref =>
    match ref with
    | .val _ => .val (.primitive "invalid-ref")
    | .trm trm => trm
  fwdRoundtrip := by
    intro trm
    rfl

unsafe example : ((Trm.false : Trm RuntimeRef).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.false : Trm RuntimeRef).eval 1) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.false : Trm RuntimeRef).eval 2) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.idFnOnFalse : Trm RuntimeRef).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.idFnOnFalse : Trm RuntimeRef).eval 2) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.get1stOnTuple : Trm RuntimeRef).eval 1) = .outOfFuel := by
  rfl

unsafe example : ((Trm.get1stOnTuple : Trm RuntimeRef).eval 3) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.get2ndOnTuple : Trm RuntimeRef).eval 3) =
    .some ((Val.primitive "true") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.apply1stOn2ndFnOnTuple : Trm RuntimeRef).eval 2) = .outOfFuel := by
  rfl

unsafe example : ((Trm.apply1stOn2ndFnOnTuple : Trm RuntimeRef).eval 4) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.applyidFnOnItself : Trm RuntimeRef).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.applyidFnOnItself : Trm RuntimeRef).eval 2) =
    .some ((Val.idFn : Val RuntimeRef)) := by
  rfl

unsafe example : ((Trm.idFnOnFalse2 : Trm RuntimeRef).eval 1) = .outOfFuel := by
  rfl

unsafe example : ((Trm.idFnOnFalse2 : Trm RuntimeRef).eval 3) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.malformedPrimitiveApply : Trm RuntimeRef).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.malformedPrimitiveApply : Trm RuntimeRef).eval 2) = .error := by
  rfl

end eval

section compile

unsafe example : ((Trm.false : Trm RuntimeRef).compile 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.false : Trm RuntimeRef).compile 1) =
    .some ((Trm.false : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.true : Trm RuntimeRef).compile 1) =
    .some ((Trm.true : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.idFn : Trm RuntimeRef).compile 1) =
    .some ((Trm.idFn : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.idFnOnFalse : Trm RuntimeRef).compile 3) =
    .some ((Trm.false : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.get1st : Trm RuntimeRef).compile 1) =
    .some ((Trm.get1st : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.get2nd : Trm RuntimeRef).compile 1) =
    .some ((Trm.get2nd : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.get1stOnTuple : Trm RuntimeRef).compile 4) =
    .some ((Trm.false : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.get2ndOnTuple : Trm RuntimeRef).compile 4) =
    .some ((Trm.true : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.apply1stOn2ndFn : Trm RuntimeRef).compile 1) =
    .some ((Trm.apply1stOn2ndFn : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.apply1stOn2ndFnOnTuple : Trm RuntimeRef).compile 5) =
    .some ((Trm.false : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.applyidFnOnItself : Trm RuntimeRef).compile 3) =
    .some ((Trm.idFn : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.idFnOnFalse2 : Trm RuntimeRef).compile 4) =
    .some ((Trm.false : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.malformedPrimitiveApply : Trm RuntimeRef).compile 2) = .error := by
  rfl

unsafe example : ((Trm.annotatedFalse : Trm RuntimeRef).compile 1) =
    .some ((Trm.false : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.annotatedIdFn : Trm RuntimeRef).compile 1) =
    .some ((Trm.idFn : Trm RuntimeRef)) := by
  rfl

unsafe example : ((Trm.annotatedIdFnOnFalse : Trm RuntimeRef).compile 3) =
    .some ((Trm.false : Trm RuntimeRef)) := by
  rfl

unsafe example :
    (((.val (.fn (body := fun x => .ref x) (tIn := none)) (some .primitive)) :
      Trm RuntimeRef).compile 1) = .error := by
  rfl

section soundness

unsafe example :
    ∃ compiled,
      (Trm.false : Trm RuntimeRef).compile 1 = .some compiled ∧
        (Trm.false : Trm RuntimeRef).Adequate compiled 1 :=
  Trm.soundness (source := (Trm.false : Trm RuntimeRef)) (fuel := 1) (by
    unfold Lp2lc.Active.DTLC.Trm.Typing
    rfl)

end soundness

end compile

end Trm

end Sanity
