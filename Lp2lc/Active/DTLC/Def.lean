import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

universe u v

-- 1. Implicitly lift a type to a higher universe using ULift
/-- Coerce a lower-universe type into a higher universe through `ULift`. -/
instance _autoUliftType : Coe (Type u) (Type (max u v)) where
  coe := ULift

-- 2. Implicitly lift the values of that type into the ULift wrapper, these 2 enabled universe cumulativity in rocq
/-- Coerce a value into the `ULift` carrier chosen by the lifted type. -/
instance _autoUliftValue {α : Type u} : Coe α (ULift.{v, u} α) where
  coe := ULift.up

structure K : Type

abbrev K1: Type 1 := K

open Util

/-- Universe-1 carrier for PHOAS indices. -/
abbrev Index := Type

section Syntax

variable (I : Index) -- index

mutual

inductive Typ : Index where
| primitive
| depFn (tIn : Typ) (tOut : (arg : I) -> Typ)
| top -- type of anything, can bind both primitive and depFn.

inductive Trm : Index where
| val (v : Val)
| depApply (fn : Trm) (arg : Trm)

inductive Val : Index where
| primitive (repr : ByteCode)
| depFn (body : (arg : I) -> Trm)
-- deriving DecidableEq

end

instance valIsTrm : Coe (Val I) (Trm I) where
  coe := (fun v => Trm.val v)

end Syntax

class FBound (I : Index) where -- fixed-point cast, looks like a reversed Env, it cast `Trm I` into something Val.depFn can accept
  fwd: Val I -> I -- useful in eval, definition uses the inverse but interpreter is not allowed to see it.

class Correspondence (I : Index) extends FBound I where
  equiv: Val I = I
  fwd := equiv.mp
  rev := equiv.mpr
  rev_fwd : (value : Val I) -> rev (fwd value) = value := by
    intro value
    cases equiv
    rfl

abbrev TypAST := {I : Index} -> [Correspondence I] -> Typ I

abbrev ValAST := {I : Index} -> [Correspondence I] -> Val I

abbrev TrmAST := {I : Index} -> [Correspondence I] -> Trm I

/-- Normalizes source terms to values while spending fuel at each semantic descent -/
def Trm.eval {I : Index} [FBound I] (trm : Trm I) (fuel : Nat) : Option (Val I) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match trm with
    | .val value => some value
    | .depApply fn arg =>
      match fn.eval fuel, arg.eval fuel with
      | some (.depFn body), some value => (body (FBound.fwd value)).eval fuel
      | _, _ => none

-- /-- TODO: this is the same eval with function body evaluation, nto sure if it is needed -/
-- def Trm.eval {I : Index} [FBound I] (trm : Trm I) (fuel : Nat) : Option (Val I) :=
--   match fuel with
--   | 0 => none
--   | fuel + 1 =>
--     match trm with
--     | .val (.depFn body) =>
--       some (.depFn (body := fun arg =>
--         let result := body arg
--         match result.eval fuel with
--         | some value => .val value
--         | none => result))
--     | .val value => some value
--     | .depApply fn arg =>
--       match fn.eval fuel, arg.eval fuel with
--       | some (.depFn body), some value => (body (FBound.fwd value)).eval fuel
--       | _, _ => none

end DTLC

end Lp2lc.Active
