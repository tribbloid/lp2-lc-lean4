import Tests.DTLC.ValSpec

namespace Tests.DTLC.Sanity
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

example {I : Index} [FBound I Val] :
    (idFnOnFalse : Trm I) =
      .apply (idFn : Trm I) (false : Trm I) := rfl

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

example {I : Index} [FBound I Val] :
    (get2ndOnTuple : Trm I) =
      .apply (.apply (get2nd : Trm I) (false : Trm I)) (true : Trm I) := rfl

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

example {I : Index} [FBound I Val] :
    (apply1stOn2ndFnOnTuple : Trm I) =
      .apply
        (.apply (apply1stOn2ndFn : Trm I) (idFn : Trm I))
        (false : Trm I) := rfl

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

example {I : Index} : ¬ (annotatedFalse : Trm I).IsTypeErased := by
  simp [annotatedFalse, Lp2lc.Active.DTLC.Trm.IsTypeErased]

example {I : Index} :
    (annotatedFalse : Trm I).eraseType = (false : Trm I) := rfl

example {I : Index} :
    (annotatedIdFn : Trm I).eraseType =
      .val (.fn (body := fun x => .ref x) (tIn := none)) none := rfl

example {I : Index} :
    (annotatedIdFnOnFalse : Trm I).eraseType =
      .apply (annotatedIdFn : Trm I).eraseType (false : Trm I) none := rfl

example {I : Index} :
    ((annotatedIdFnOnFalse : Trm I).eraseType).IsTypeErased :=
  eraseType_isErased I (annotatedIdFnOnFalse : Trm I)

-- evaulation

variable {I : Index} [FBound I Val]

attribute [local simp] Trm.eval Trm.false Trm.true Trm.idFn Trm.idFnOnFalse
attribute [local simp] Trm.get1st Trm.get2nd Trm.get1stOnTuple Trm.get2ndOnTuple
attribute [local simp] Trm.apply1stOn2ndFn Trm.apply1stOn2ndFnOnTuple
attribute [local simp] Trm.applyidFnOnItself Trm.idFnOnFalse2

example : ((Trm.false : Trm I).eval 0) = .outOfFuel := rfl
example : ((Trm.false : Trm I).eval 1) = .some ((Val.primitive "false") : Val I) := rfl
example : ((Trm.false : Trm I).eval 2) = .some ((Val.primitive "false") : Val I) := rfl
example : ((Trm.idFnOnFalse : Trm I).eval 0) = .outOfFuel := rfl

example : ((Trm.idFnOnFalse : Trm I).eval 2) =
    .some ((Val.primitive "false") : Val I) := by
  simp

example : ((Trm.get1stOnTuple : Trm I).eval 1) = .outOfFuel := rfl

example : ((Trm.get1stOnTuple : Trm I).eval 3) =
    .some ((Val.primitive "false") : Val I) := by
  simp

example : ((Trm.get2ndOnTuple : Trm I).eval 3) =
    .some ((Val.primitive "true") : Val I) := by
  simp

example : ((Trm.apply1stOn2ndFnOnTuple : Trm I).eval 2) = .outOfFuel := rfl

example : ((Trm.apply1stOn2ndFnOnTuple : Trm I).eval 4) =
    .some ((Val.primitive "false") : Val I) := by
  simp

example : ((Trm.applyidFnOnItself : Trm I).eval 0) = .outOfFuel := rfl

example : ((Trm.applyidFnOnItself : Trm I).eval 2) =
    .some ((Val.idFn : Val I)) := by
  simp [Val.idFn]

example : ((Trm.idFnOnFalse2 : Trm I).eval 1) = .outOfFuel := rfl

example : ((Trm.idFnOnFalse2 : Trm I).eval 3) =
    .some ((Val.primitive "false") : Val I) := by
  simp

example : ((Trm.malformedPrimitiveApply : Trm I).eval 0) = .outOfFuel := rfl

example : ((Trm.malformedPrimitiveApply : Trm I).eval 2) = .error := rfl

end Trm

end Sanity
