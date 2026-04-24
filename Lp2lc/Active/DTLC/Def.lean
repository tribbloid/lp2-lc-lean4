import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus, STLC but function output type can depend on input term.
-/

open Util

universe u

section Syntax

variable (I : Sort u) -- index

mutual

inductive Typ : Type (u + 1) where
| primitive : Typ
| depFn (tIn : Typ) (tOut : (arg : I) -> Typ) : Typ

inductive Trm : Type (u + 1) where
| var (symbol : I) (tAnnotation : Typ) : Trm
| val (v : Val) : Trm
| depApply (fn : Trm) (arg : Trm) : Trm

inductive Val : Type (u + 1) where
| primitive (repr : ByteCode) : Val
| depFn (body : (arg : I) -> Trm) : Val
end

end Syntax

abbrev TrmClosed := {I : Sort 1} -> Trm I

abbrev TypClosed := {I : Sort 1} -> Typ I

abbrev ByteCodeTrm := Trm ByteCode

section Semantics

@[simp]
private def runtime_eval_bytecode : Nat -> ByteCodeTrm -> Option ByteCodeTrm
  | 0, _ => none
  | fuel + 1, trm =>
      match trm with
      | Trm.var symbol _ => some (Trm.val (Val.primitive symbol))
      | Trm.val (Val.primitive repr) => some (Trm.val (Val.primitive repr))
      | Trm.val (Val.depFn body) => some (Trm.val (Val.depFn body))
      | Trm.depApply fn arg =>
          match runtime_eval_bytecode fuel fn, runtime_eval_bytecode fuel arg with
          | some (Trm.val (Val.depFn body)), some (Trm.val (Val.primitive argByte)) =>
              runtime_eval_bytecode fuel (body argByte)
          | _, _ => none

@[simp]
private def typing_bytecode : Nat -> ByteCodeTrm -> Typ ByteCode -> Prop
  | 0, _, _ => False
  | fuel + 1, trm, typ =>
      match trm with
      | Trm.var _ tAnnotation => tAnnotation = typ
      | Trm.val (Val.primitive _) => typ = Typ.primitive
      | Trm.val (Val.depFn body) =>
          match typ with
          | Typ.primitive => False
          | Typ.depFn tIn tOut =>
              ∀ arg : ByteCode,
                typing_bytecode fuel (Trm.val (Val.primitive arg)) tIn ->
                typing_bytecode fuel (body arg) (tOut arg)
      | Trm.depApply fn arg =>
          ∃ tIn tOut argByte,
            typing_bytecode fuel fn (Typ.depFn tIn tOut) ∧
            typing_bytecode fuel arg tIn ∧
            runtime_eval_bytecode fuel arg = some (Trm.val (Val.primitive argByte)) ∧
            typ = tOut argByte

@[simp]
def runtime_eval (fuel : Nat) (trm : TrmClosed) : Option ByteCodeTrm :=
  runtime_eval_bytecode fuel (trm (I := ByteCode))

@[simp]
def typing (fuel : Nat) (trm : TrmClosed) (typ : TypClosed) : Prop :=
  typing_bytecode fuel (trm (I := ByteCode)) (typ (I := ByteCode))

end Semantics

end DTLC

end Lp2lc.Active
