import «Lp2lc».Active.DOT.Def



/-
this is a supporting sanity test file for DOT calculus syntax definition.

each of the AST below are supposed to represent scala variable of the same name
in @SanityExample.scala
-/

namespace Tests.DOT.Sanity
open Lp2lc.Active.DOT

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


/-
Object/record term/type in Scala requires some elaboration, as DOT only contains structural typing:

- structural type with 1 unbounded type alias is a single "Entry.typeAlias"
-

-/

end Trm
end Sanity
