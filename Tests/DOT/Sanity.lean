import «Lp2lc».Active.DOT.Def



/-
this is a supporting sanity test file for DOT calculus syntax definition.

each of the AST below are supposed to represent scala variable of the same name
in @SanityExample.scala
-/

namespace Tests.DOT.Sanity
open Lp2lc.Active.DOT
open Lp2lc.Active.Util

private def emptyBody {I : Type} : ObjectBody I :=
  { lookup := fun _ => none }

private def singletonBody {I : Type} (name : Name) (entry : MemberImpl I) :
    ObjectBody I :=
  { lookup := fun key => if key = name then some entry else none }

private def namedTermImpl {I : Type} (name : Name) (body : Trm I) (annotation : Typ I) :
    MemberImpl I :=
  .term (some name) body annotation

private def implicitSubtypeEntry {I : Type} (tUnder tOver : Typ I) :
    MemberDeclaration I :=
  .term none true (.evidence (.subtypeEv tUnder tOver))

private def selfMemberTyp {I : Type} (this : I) (name : Name) : Typ I :=
  .depSelectTyp (.var this .top) name

namespace Trm

def false : TrmClosed :=
  .val (.primitive "false")

def true : TrmClosed :=
  .val (.primitive "true")

def identityFn : TrmClosed :=
  .val
    (.depFn (fun x => .var x .primitive))

def identityFnOnFalse : TrmClosed :=
  .depApply identityFn false

def get1st : TrmClosed :=
  .val
    (.depFn (fun x =>
      .val
        (.depFn (fun _y => .var x .primitive))))

def get2nd : TrmClosed :=
  .val
    (.depFn (fun _x =>
      .val
        (.depFn (fun y => .var y .primitive))))

def get1stOnTuple : TrmClosed :=
  .depApply
    (.depApply get1st false)
    true

def get2ndOnTuple : TrmClosed :=
  .depApply
    (.depApply get2nd false)
    true

def apply1stOn2ndFn : TrmClosed :=
  .val (.depFn (fun f =>
    .val (.depFn (fun x =>
      .depApply
        (.var f (.depFn .primitive (fun _ => .primitive)))
        (.var x .primitive)))))

def apply1stOn2ndFnOnTuple : TrmClosed :=
  .depApply
    (.depApply apply1stOn2ndFn identityFn)
    false

def structural1Trm : TrmClosed :=
  .val
    (.object (fun _this =>
      singletonBody "a"
        (namedTermImpl "a" (.val (.primitive "false")) .primitive)))

def structural1Typ : TrmClosed :=
  .val
    (.object (fun _this =>
      singletonBody "A" (.typeAlias "A")))

def structural1Bounded : TrmClosed :=
  .val
    (.object (fun _this =>
      emptyBody))

end Trm

namespace Typ

def false : TypClosed :=
  .primitive

def true : TypClosed :=
  .primitive

def identityFn : TypClosed :=
  .depFn .primitive (fun _x => .primitive)

def identityFnOnFalse : TypClosed :=
  .primitive

def get1st : TypClosed :=
  .depFn .primitive (fun _x =>
    .depFn .primitive (fun _y => .primitive))

def get2nd : TypClosed :=
  .depFn .primitive (fun _x =>
    .depFn .primitive (fun _y => .primitive))

def get1stOnTuple : TypClosed :=
  .primitive

def get2ndOnTuple : TypClosed :=
  .primitive

def apply1stOn2ndFn : TypClosed :=
  .depFn
    (.depFn .primitive (fun _x => .primitive))
    (fun _f =>
      .depFn .primitive (fun _x => .primitive))

def apply1stOn2ndFnOnTuple : TypClosed :=
  .primitive

def structural1Trm : TypClosed :=
  .selfBinder (fun _this =>
    .oneMember (.term (some "a") Bool.false .primitive))

def structural1Typ : TypClosed :=
  .selfBinder (fun _this =>
    .oneMember (.typeAlias "A"))

def EmptyTrait : TypClosed :=
  .selfBinder (fun _this =>
    .oneMember (.typeAlias "class_EmptyTrait"))

def structural1Bounded : TypClosed :=
  .selfBinder (fun this =>
    .and
      (.oneMember (.typeAlias "A"))
      (.and
        (.oneMember
          (implicitSubtypeEntry .bottom (selfMemberTyp this "A")))
        (.oneMember
          (implicitSubtypeEntry
            (selfMemberTyp this "A")
            EmptyTrait))))

def SubTrait : TypClosed :=
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
