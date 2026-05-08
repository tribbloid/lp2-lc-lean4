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
- must include all test cases from "Sanity.Trm" & "Sanity.Eval" namespace.

-/

/-- Pure handle codes used by the concrete V2 sanity carrier. -/
inductive Handle : Type where
| primitive (repr : String)
| idFn
| const (value : Handle)
| get1st
| get2nd
| apply1stOn2ndFn
| applyClosure (fn : Handle)
| unknown
  deriving DecidableEq, Repr

/-- Concrete value syntax over handles. -/
def ValAST := Val Handle

/-- Concrete term syntax over handles. -/
def TrmAST := Trm Handle

/-- Fixed unfolding depth for the pure handle cache. -/
private def cache_fuel : Nat := 16

/-- Stuck term returned when a handle cannot be reified. -/
private def miss : TrmAST :=
  .val (.primitive "stuck")

mutual

/-- Reifies a handle to the value it records while spending cache fuel. -/
private def Handle.get_trm_fuel (fuel : Nat) (self : Handle) : Option ValAST :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match self with
    | .primitive repr => some (.primitive repr)
    | .idFn => some (.fn (body := fun x => x.get_trm_term fuel))
    | .const value => some (.fn (body := fun _x => value.get_trm_term fuel))
    | .get1st =>
      some (.fn (body := fun x =>
        .val (.fn (body := fun _y => x.get_trm_term fuel))))
    | .get2nd =>
      some (.fn (body := fun _x =>
        .val (.fn (body := fun y => y.get_trm_term fuel))))
    | .apply1stOn2ndFn =>
      some (.fn (body := fun f =>
        .val (.fn (body := fun x =>
          .depApply (f.get_trm_term fuel) (x.get_trm_term fuel)))))
    | .applyClosure fn =>
      some (.fn (body := fun x =>
        .depApply (fn.get_trm_term fuel) (x.get_trm_term fuel)))
    | .unknown => none

/-- Reifies a handle as a term while spending cache fuel. -/
private def Handle.get_trm_term (self : Handle) (fuel : Nat) : TrmAST :=
  match self.get_trm_fuel fuel with
  | some value => .val value
  | none => miss

end

mutual

/-- Computes the best handle code available for a value. -/
private def val_handle_fuel (fuel : Nat) (self : ValAST) : Handle :=
  match fuel with
  | 0 => .unknown
  | fuel + 1 =>
    match self with
    | .primitive repr => .primitive repr
    | .fn body =>
      let x : Handle := .primitive "__probe_x"
      let y : Handle := .primitive "__probe_y"
      match body x with
      | .val (.fn inner) =>
        match inner y with
        | .val value =>
          let handle := val_handle_fuel fuel value
          if handle = x then
            .get1st
          else if handle = y then
            .get2nd
          else
            .const (.const handle)
        | .depApply fn arg =>
          if term_handle_fuel fuel fn = x ∧ term_handle_fuel fuel arg = y then
            .apply1stOn2ndFn
          else
            .unknown
      | .val value =>
        let handle := val_handle_fuel fuel value
        if handle = x then
          .idFn
        else
          .const handle
      | .depApply fn arg =>
        if term_handle_fuel fuel arg = x then
          .applyClosure (term_handle_fuel fuel fn)
        else
          .unknown

/-- Computes a handle for a term when the term is already a value. -/
private def term_handle_fuel (fuel : Nat) (self : TrmAST) : Handle :=
  match self with
  | .val value => val_handle_fuel fuel value
  | .depApply _fn _arg => .unknown

end

/-- generate a new handle if `self` is new, otherwise return the old handle -/
def Val!.getHandle (self : ValAST) : Handle :=
  val_handle_fuel cache_fuel self

/-- return some if it's handle has been generated before, otherwise return none -/
def Handle.getTrm (self : Handle) : Option ValAST :=
  self.get_trm_fuel cache_fuel

instance : FBound Handle where
  fwd := Val!.getHandle

/-- Converts a known handle back into a term. -/
def Handle.getTrmTerm (self : Handle) : TrmAST :=
  match self.getTrm with
  | some value => .val value
  | none => miss

/-- Primitive false term. -/
def false : TrmAST :=
  .val (.primitive "false")

/-- Primitive true term. -/
def true : TrmAST :=
  .val (.primitive "true")

/-- Identity function term. -/
def idFn : TrmAST :=
  .val (.fn (body := fun x => x.getTrmTerm))

/-- Identity function applied to false. -/
def idFnOnFalse : TrmAST :=
  .depApply idFn false

example : idFnOnFalse = .depApply idFn false := rfl

/-- First projection encoded as nested functions. -/
def get1st : TrmAST :=
  .val
    (.fn (body := fun x =>
      .val
        (.fn (body := fun _y => x.getTrmTerm))))

/-- Second projection encoded as nested functions. -/
def get2nd : TrmAST :=
  .val
    (.fn (body := fun _x =>
      .val
        (.fn (body := fun y => y.getTrmTerm))))

/-- First projection applied to a false/true tuple. -/
def get1stOnTuple : TrmAST :=
  .depApply
    (.depApply get1st false)
    true

/-- Second projection applied to a false/true tuple. -/
def get2ndOnTuple : TrmAST :=
  .depApply
    (.depApply get2nd false)
    true

example : get2ndOnTuple = .depApply (.depApply get2nd false) true := rfl

/-- Applies its first argument to its second argument. -/
def apply1stOn2ndFn : TrmAST :=
  .val (.fn (body := fun f =>
      .val (.fn (body := fun x =>
        .depApply
          f.getTrmTerm
          x.getTrmTerm))))

/-- Applies `apply1stOn2ndFn` to `idFn` and false. -/
def apply1stOn2ndFnOnTuple : TrmAST :=
  .depApply
    (.depApply apply1stOn2ndFn idFn)
    false

example : apply1stOn2ndFnOnTuple = .depApply (.depApply apply1stOn2ndFn idFn) false := rfl

/-- Identity function applied to itself. -/
def applyidFnOnItself : TrmAST :=
  .depApply idFn idFn

/-- Self-applied identity function applied to false. -/
def idFnOnFalse2 : TrmAST :=
  .depApply applyidFnOnItself false

/-- Malformed primitive application used as a stuck evaluator case. -/
def malformedPrimitiveApply : TrmAST :=
  .depApply false true

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
