import «Lp2lc».Active.DOT.DOTDef



/-
this is a supporting sanity test file for DOT calculus syntax definition.

the related Scala syntax examples live under [[../Example]]
-/

namespace Tests.DOT.Sanity
open Lp2lc.Active.DOT
open Lp2lc.Active.Util

private def emptyBody {I : Type} {ByteCode : Type} : ObjectBody I ByteCode :=
  { lookup := fun _ => none }

private def singletonBody {I : Type} {ByteCode : Type} (name : Name) (entry : MemberImpl I ByteCode) :
    ObjectBody I ByteCode :=
  { lookup := fun key => if key = name then some entry else none }

private def namedTermImpl {I : Type} {ByteCode : Type} (name : Name)
    (body : Trm I ByteCode) (annotation : Typ I ByteCode) :
    MemberImpl I ByteCode :=
  .term (some name) body annotation

private def implicitSubtypeEntry {I : Type} {ByteCode : Type} (tUnder tOver : Typ I ByteCode) :
    MemberDeclaration I ByteCode :=
  .term none true (.evidence (.subtypeEv tUnder tOver))

private def selfMemberTyp {I : Type} {ByteCode : Type} (this : I) (name : Name) : Typ I ByteCode :=
  .depSelectTyp (.var this .top) name

namespace Trm

def false : TrmClosed String :=
  .val (.primitive "false")

def true : TrmClosed String :=
  .val (.primitive "true")

def identityFn : TrmClosed String :=
  .val
    (.depFn (fun x => .var x .primitive))

def identityFnOnFalse : TrmClosed String :=
  .depApply identityFn false

def get1st : TrmClosed String :=
  .val
    (.depFn (fun x =>
      .val
        (.depFn (fun _y => .var x .primitive))))

def get2nd : TrmClosed String :=
  .val
    (.depFn (fun _x =>
      .val
        (.depFn (fun y => .var y .primitive))))

def get1stOnTuple : TrmClosed String :=
  .depApply
    (.depApply get1st false)
    true

def get2ndOnTuple : TrmClosed String :=
  .depApply
    (.depApply get2nd false)
    true

def apply1stOn2ndFn : TrmClosed String :=
  .val (.depFn (fun f =>
    .val (.depFn (fun x =>
      .depApply
        (.var f (.depFn .primitive (fun _ => .primitive)))
        (.var x .primitive)))))

def apply1stOn2ndFnOnTuple : TrmClosed String :=
  .depApply
    (.depApply apply1stOn2ndFn identityFn)
    false

def structural1Trm : TrmClosed String :=
  .val
    (.object (fun _this =>
      singletonBody "a"
        (namedTermImpl "a" (.val (.primitive "false")) .primitive)))

def structural1Typ : TrmClosed String :=
  .val
    (.object (fun _this =>
      singletonBody "A" (.typeAlias "A")))

def structural1Bounded : TrmClosed String :=
  .val
    (.object (fun _this =>
      emptyBody))

end Trm

namespace Typ

def false : TypClosed String :=
  .primitive

def true : TypClosed String :=
  .primitive

def identityFn : TypClosed String :=
  .depFn .primitive (fun _x => .primitive)

def identityFnOnFalse : TypClosed String :=
  .primitive

def get1st : TypClosed String :=
  .depFn .primitive (fun _x =>
    .depFn .primitive (fun _y => .primitive))

def get2nd : TypClosed String :=
  .depFn .primitive (fun _x =>
    .depFn .primitive (fun _y => .primitive))

def get1stOnTuple : TypClosed String :=
  .primitive

def get2ndOnTuple : TypClosed String :=
  .primitive

def apply1stOn2ndFn : TypClosed String :=
  .depFn
    (.depFn .primitive (fun _x => .primitive))
    (fun _f =>
      .depFn .primitive (fun _x => .primitive))

def apply1stOn2ndFnOnTuple : TypClosed String :=
  .primitive

def structural1Trm : TypClosed String :=
  .selfBinder (fun _this =>
    .oneMember (.term (some "a") Bool.false .primitive))

def structural1Typ : TypClosed String :=
  .selfBinder (fun _this =>
    .oneMember (.typeAlias "A"))

def emptyTrait : TypClosed String :=
  .selfBinder (fun _this =>
    .oneMember (.typeAlias "class_EmptyTrait"))

def structural1Bounded : TypClosed String :=
  .selfBinder (fun this =>
    .and
      (.oneMember (.typeAlias "A"))
      (.and
        (.oneMember
          (implicitSubtypeEntry .bottom (selfMemberTyp this "A")))
        (.oneMember
          (implicitSubtypeEntry
            (selfMemberTyp this "A")
            emptyTrait))))

def subTrait : TypClosed String :=
  .selfBinder (fun this =>
    .and
      (.oneMember (.typeAlias "class_EmptyTrait"))
      (.and
        (.oneMember (.typeAlias "class_SubTrait"))
        (.oneMember
          (implicitSubtypeEntry
            (selfMemberTyp this "class_SubTrait")
            (selfMemberTyp this "class_EmptyTrait")))))

end Typ
end Sanity
