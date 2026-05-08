import «Lp2lc».Active.DTLC.Def



/-
this is a supporting sanity test file for DOT calculus syntax definition.

each of the AST below are supposed to represent scala variable of the same name
in @SanityExample.scala
-/

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC

namespace Val

def idFn : ValAST :=
  .fn (body := fun x => Correspondence.rev x)

end Val

namespace TrmWithHandle

/-
simple rig for generating a Handle for each Val! and cache the bijection

this is only for sanity examples, not core syntax. It is possible to include an environment or cache inside the handle.

functions don't have extensional equality. So for `fn`, `getHandle` should
always return a new Handle, which can be used in `getTrm` to get the original
`fn`. This should be tested in a case.

Your implementation:

- cannot use mutable data structure or IO.
- must include all test cases from "Trm" namespace
-/

inductive Handle where
| primitive (repr : String)
| fn
deriving Hashable, DecidableEq

def Val! := Val Handle

/-- generate a new handle if `self` is new, otherwise return the old handle -/
def Val!.getHandle (self: Val!) : Handle :=
  match self with
  | .primitive repr => .primitive repr
  | .fn _body => .fn

/-- return some if it's handle has been generated before, otherwise return none -/
def Handle.getTrm (self: Handle) : Option Val! :=
  match self with
  | .primitive repr => some (.primitive repr)
  | .fn => none

instance fb : FBound Handle where
  fwd := Val!.getHandle

example :
    Handle.getTrm (Val!.getHandle (.primitive "false")) =
      some (.primitive "false") := rfl

example :
    Handle.getTrm (Val!.getHandle (.fn (body := fun _arg => .val (.primitive "false")))) =
      none := rfl

def false : Trm Handle :=\,,
  .val (.primitive "false")

def idFn : Trm Handle :=
  .val
    (.fn (body := fun arg =>
      match arg.getTrm with
      | some value => .val value
      | none => .val (.primitive "stuck")))

def idFnOnFalse : Trm Handle :=
  .depApply idFn false

example : false.eval 1 = some (.primitive "false") := rfl

example : idFnOnFalse.eval 2 = some (.primitive "false") := rfl


end TrmWithHandle

namespace Trm

def false : TrmAST :=
  .val (.primitive "false")

def true : TrmAST :=
  .val (.primitive "true")

def idFn : TrmAST :=
  .val (.fn (body := fun x => Correspondence.rev x))

def idFnOnFalse : TrmAST :=
  .depApply idFn false

example {I : Index} [Correspondence I] :
    (idFnOnFalse : Trm I) =
      .depApply (idFn : Trm I) (false : Trm I) := rfl

def get1st : TrmAST :=
  .val
    (.fn (body := fun x =>
      .val
        (.fn (body := fun _y => Correspondence.rev x))))

def get2nd : TrmAST :=
  .val
    (.fn (body := fun _x =>
      .val
        (.fn (body := fun y => Correspondence.rev y))))

def get1stOnTuple : TrmAST :=
  .depApply
    (.depApply get1st false)
    true

def get2ndOnTuple : TrmAST :=
  .depApply
    (.depApply get2nd false)
    true

example {I : Index} [Correspondence I] :
    (get2ndOnTuple : Trm I) =
      .depApply (.depApply (get2nd : Trm I) (false : Trm I)) (true : Trm I) := rfl

def apply1stOn2ndFn : TrmAST :=
  .val (.fn (body := fun f =>
      .val (.fn (body := fun x =>
        .depApply
          (Correspondence.rev f)
          (Correspondence.rev x)))))

def apply1stOn2ndFnOnTuple : TrmAST :=
  .depApply
    (.depApply apply1stOn2ndFn idFn)
    false

example {I : Index} [Correspondence I] :
    (apply1stOn2ndFnOnTuple : Trm I) =
      .depApply
        (.depApply (apply1stOn2ndFn : Trm I) (idFn : Trm I))
        (false : Trm I) := rfl

def applyidFnOnItself : TrmAST :=
  .depApply idFn idFn

def idFnOnFalse2 : TrmAST :=
  .depApply applyidFnOnItself false

def malformedPrimitiveApply : TrmAST :=
  .depApply false true

end Trm

namespace Typ

def false : TypAST :=
  .primitive

def idFn : TypAST :=
  .depFn .primitive (fun _x => .primitive)

def get1st : TypAST :=
  .depFn .primitive (fun _x =>
    .depFn .primitive (fun _y => .primitive))

def apply1stOn2ndFn : TypAST :=
  .depFn
    (.depFn .primitive (fun _x => .primitive))
    (fun _f =>
      .depFn .primitive (fun _x => .primitive))

end Typ

namespace Eval

variable {I : Index} [Correspondence I]

example : ((Trm.false : Trm I).eval 0) = none := rfl
example : ((Trm.false : Trm I).eval 1) = some ((Val.primitive "false") : Val I) := rfl
example : ((Trm.false : Trm I).eval 2) = some ((Val.primitive "false") : Val I) := rfl
example : ((Trm.idFnOnFalse : Trm I).eval 0) = none := rfl

example : ((Trm.idFnOnFalse : Trm I).eval 2) =
    some ((Val.primitive "false") : Val I) := by
  simp [Trm.eval, Trm.idFnOnFalse, Trm.idFn, Trm.false, Correspondence.rev_fwd]

example : ((Trm.get1stOnTuple : Trm I).eval 1) = none := rfl

example : ((Trm.get1stOnTuple : Trm I).eval 3) =
    some ((Val.primitive "false") : Val I) := by
  simp [Trm.eval, Trm.get1stOnTuple, Trm.get1st, Trm.false, Trm.true,
    Correspondence.rev_fwd]

example : ((Trm.get2ndOnTuple : Trm I).eval 3) =
    some ((Val.primitive "true") : Val I) := by
  simp [Trm.eval, Trm.get2ndOnTuple, Trm.get2nd, Trm.false, Trm.true,
    Correspondence.rev_fwd]

example : ((Trm.apply1stOn2ndFnOnTuple : Trm I).eval 2) = none := rfl

example : ((Trm.apply1stOn2ndFnOnTuple : Trm I).eval 4) =
    some ((Val.primitive "false") : Val I) := by
  simp [Trm.eval, Trm.apply1stOn2ndFnOnTuple, Trm.apply1stOn2ndFn, Trm.idFn,
    Trm.false, Correspondence.rev_fwd]

example : (((Trm.applyidFnOnItself : Trm I).eval 0).isNone) = true := rfl

example : (((Trm.applyidFnOnItself : Trm I).eval 2).isSome) = true := by
  simp [Trm.eval, Trm.applyidFnOnItself, Trm.idFn, Correspondence.rev_fwd]

example : ((Trm.idFnOnFalse2 : Trm I).eval 1) = none := rfl

example : ((Trm.idFnOnFalse2 : Trm I).eval 3) =
    some ((Val.primitive "false") : Val I) := by
  simp [Trm.eval, Trm.idFnOnFalse2, Trm.applyidFnOnItself, Trm.idFn, Trm.false,
    Correspondence.rev_fwd]

end Eval

-- namespace Eval

-- example : Definitional.eval Trm.idFnOnFalse 0 = none := rfl

-- example :
--     Definitional.eval Trm.idFnOnFalse 1 =
--       some ((Val.primitive "false") : Val PUnit) := rfl

-- example :
--     Denotational.eval Trm.idFnOnFalse 1 =
--       some ((Val.primitive "false") : Val PUnit) := rfl

-- example : Definitional.eval Trm.get1stOnTuple 1 = none := rfl

-- example :
--     Definitional.eval Trm.get1stOnTuple 2 =
--       some ((Val.primitive "false") : Val PUnit) := rfl

-- example :
--     Denotational.eval Trm.get2ndOnTuple 2 =
--       some ((Val.primitive "true") : Val PUnit) := rfl

-- example : Definitional.eval Trm.apply1stOn2ndFnOnTuple 2 = none := rfl

-- example :
--     Definitional.eval Trm.apply1stOn2ndFnOnTuple 3 =
--       some ((Val.primitive "false") : Val PUnit) := rfl

-- example : Definitional.eval (.depApply Trm.idFn Trm.idFn) 1 = none := rfl

-- end Eval

-- namespace Typing

-- example : TrmClosed.typing Trm.false 2 Typ.false := by
--   simp [TrmClosed.typing, Trm.false, Typ.false]

-- example : TrmClosed.typing Trm.true 2 Typ.true := by
--   simp [TrmClosed.typing, Trm.true, Typ.true]

-- example : TrmClosed.typing Trm.idFn 3 Typ.idFn := by
--   simp [TrmClosed.typing, Trm.idFn, Typ.idFn]

-- example : TrmClosed.typing Trm.get1st 4 Typ.get1st := by
--   simp [TrmClosed.typing, Trm.get1st, Typ.get1st]

-- example : TrmClosed.typing Trm.get2nd 4 Typ.get2nd := by
--   simp [TrmClosed.typing, Trm.get2nd, Typ.get2nd]

-- example : ¬ TrmClosed.typing Trm.apply1stOn2ndFnOnTuple 6 Typ.apply1stOn2ndFnOnTuple := by
--   simp [TrmClosed.typing, Trm.apply1stOn2ndFnOnTuple, Trm.apply1stOn2ndFn, Trm.idFn,
--     Trm.false,
--     Typ.apply1stOn2ndFnOnTuple]

-- end Typing


end Sanity
