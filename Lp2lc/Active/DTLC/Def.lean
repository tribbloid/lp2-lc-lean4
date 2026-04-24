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

abbrev ByteCodeVal := Val ByteCode

section Semantics

@[simp]
private def evalBytecode (fuel : Nat) (trm : ByteCodeTrm) : Option ByteCodeVal :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match trm with
      | Trm.var symbol _ => some (Val.primitive symbol)
      | Trm.val (Val.primitive repr) => some (Val.primitive repr)
      | Trm.val (Val.depFn body) => some (Val.depFn body)
      | Trm.depApply fn arg =>
          match evalBytecode fuel fn, evalBytecode fuel arg with
          | some (Val.depFn body), some (Val.primitive argByte) =>
              evalBytecode fuel (body argByte)
          | _, _ => none

@[simp]
private def typingBytecode (fuel : Nat) (trm : ByteCodeTrm) (typ : Typ ByteCode) : Prop :=
  match fuel with
  | 0 => False
  | fuel + 1 =>
      match trm with
      | Trm.var _ tAnnotation => tAnnotation = typ
      | Trm.val (Val.primitive _) => typ = Typ.primitive
      | Trm.val (Val.depFn body) =>
          match typ with
          | Typ.primitive => False
          | Typ.depFn tIn tOut =>
              ∀ arg : ByteCode,
                typingBytecode fuel (Trm.val (Val.primitive arg)) tIn ->
                typingBytecode fuel (body arg) (tOut arg)
      | Trm.depApply fn arg =>
          ∃ tIn tOut argByte,
            typingBytecode fuel fn (Typ.depFn tIn tOut) ∧
            typingBytecode fuel arg tIn ∧
            evalBytecode fuel arg = some (Val.primitive argByte) ∧
            typ = tOut argByte

namespace TrmClosed

@[simp]
def eval (trm : TrmClosed) (fuel : Nat) : Option ByteCodeVal :=
  evalBytecode fuel (trm (I := ByteCode))

@[simp]
def typing (trm : TrmClosed) (fuel : Nat) (typ : TypClosed) : Prop :=
  typingBytecode fuel (trm (I := ByteCode)) (typ (I := ByteCode))

end TrmClosed

end Semantics

end DTLC

end Lp2lc.Active
