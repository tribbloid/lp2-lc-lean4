import «Lp2lc».Active.DTLC.Def



/-
this is a supporting sanity test file for DOT calculus syntax definition.

each of the AST below are supposed to represent scala variable of the same name
in @SanityExample.scala
-/

namespace Tests.DTLC.SanityV2
open Lp2lc.Active.DTLC

namespace Val

def idFn : ValAST :=
  .fn (body := fun x => Correspondence.rev x)

end Val


namespace Trm

/-
simple rig for generating a Handle for each Val! and cache the bijection

this is only for sanity examples, not core syntax.

It is possible to include an environment or cache inside the handle.

functions don't have extensional equality. So for `fn`, `getHandle` should
always return a new Handle, which can be used in `getTrm` to get the original
`fn`. This should be tested in a case.

both functions should retrieve in best effort is not allowed to give up prematurely.

Your implementation:

- cannot use mutable data structure or IO.
- must include all test cases from "Sanity.Trm" namespace.
- "Eval" namespace must be successful
- your code must be under 50 lines of code
-/

def Handle : Type := sorry

def ValAST := Val Handle

def TrmAST := Trm Handle

/-- generate a new handle if `self` is new, otherwise return the old handle -/
def Val!.getHandle (self: ValAST) : Handle := sorry

/-- return some if it's handle has been generated before, otherwise return none -/
def Handle.getTrm (self: Handle) : Option ValAST := sorry

instance : FBound Handle where
  fwd := Val!.getHandle

end Trm

namespace Eval

example : Trm.false.eval 0 = none := rfl
example : Trm.false.eval 1 = some (.primitive "false") := rfl
example : Trm.false.eval 2 = some (.primitive "false") := rfl
example : Trm.idFnOnFalse.eval 0 = none := rfl

example : Trm.idFnOnFalse.eval 2 = some (.primitive "false") := rfl

example : Trm.get1stOnTuple.eval 1 = none := rfl

example : Trm.get1stOnTuple.eval 3 = some (.primitive "false") := rfl

example : Trm.get2ndOnTuple.eval 3 = some (.primitive "true") := rfl

example : Trm.apply1stOn2ndFnOnTuple.eval 2 = none := rfl

example : Trm.apply1stOn2ndFnOnTuple.eval 4 = some (.primitive "false") := rfl

example : (Trm.applyidFnOnItself.eval 0).isNone = Bool.true := rfl

example : (Trm.applyidFnOnItself.eval 2).isSome = Bool.true := rfl

example : Trm.idFnOnFalse2.eval 1 = none := rfl

example : Trm.idFnOnFalse2.eval 3 = some (.primitive "false") := rfl

end Eval

end SanityV2
