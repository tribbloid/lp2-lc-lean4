import Std
import Mathlib.Data.Finset.Basic

import Aesop
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Dot

/-
here is the self-contained syntax for the latest DOT (System D-Diamond with
object/record, with real forAll).

It is:

- Not System F! (or its extension, lack of explicit polyFn, polyArrow, fake forAll)
- Not WadlerFest 2016 version! (lack of union type)
-/

/-
Recommendations:
- PHOAS, term/type indices are irrelevant, no de Bruijn serial or explicit
  variable name allowed
- All typing/subtyping/variance relations are evidences (a special kind of
  term)! These includes:
  - typing: t : T
  - subtyping: T1 <:< T2
  - variance for type constructors: [+I] => T[I], [-I] => T[I]
- Intrinsic typing but they are just built-in evidences/axioms for the symbol,
  they don't participate in judgement of inhabitance or well-typedness (these
  are still extrinsic).
- Scala is purely functional, stateless with structural object/record, so:
  - No let-binding! (exists in Wadler 2016 but was quickly removed), binding is
    just monoFn/monoApply with side effects on the record of local variables
  - Explicit Env/Context/Store is just a collection of all 3 kinds of evidences (backed
    by Heyting lattice).

    It's only an IR built from only a AST tree and nothing else, but it's an important
    one. Without it we may never be able to infer the equality of
    - `type A; type B <: A`, and
    - `type B; type A >: B`
-/

def ByteCode := String

section Syntax

variable (I: Type)[DecidableEq I][BEq I][Hashable I] -- index

def Env (V: Type) := I → Option V

namespace Env

def empty : Env I V := fun _ => none

def set (σ : Env I V) (x : I) (v : Value) : Env I V :=
  fun y => if y = x then some v else σ y

@[simp] theorem set_same (σ : Env I V) (x : I) (v : Value) :
  (σ.set x v) x = some v := by
  simp [set]

@[simp] theorem set_other (σ : Env I V) (x y : I) (v : Value) (h : y ≠ x) :
  (σ.set x v) y = σ y := by
  simp [set, h]

end Env

mutual

inductive Entry: Type where -- member of an object
| type: (Label: I) -> Typ -> Entry -- `{type Label = Ty}`
| term: (label: I) -> Trm -> Entry -- `{term label = Tm}`

inductive Typ : Type where
| primitive : Typ -- `AnyVal`, won't differentiate Int/Float/Byte.
| subtypeEv: (tUnder: Typ) -> (tOver: Typ) -> Typ -- `Under <:< Over`
| fn : (tIn :Typ) -> (tOut: Typ) -> Typ -- function, `In => Out`
| object  : Entry → Typ
| selection: I -> I -> Typ
| and: (tX: Typ) -> (tY: Typ) -> Typ -- AKA intersection, `X & Y`
| or: (tX: Typ) -> (tY: Typ) -> Typ -- AKA union, `X | Y`
| top  : Typ -- `Any`
| bottom  : Typ -- `Nothing`

inductive Val : Type where -- evaluation results and args of Atomic Normal Form (ANF)
| object : (self: Typ) → Env I Entry → Val -- carrying a self type together with member definitions
-- Function value with input type annotation and body
| fn : (body : (arg: I) -> Trm) -> Trm
deriving Repr, DecidableEq

inductive Trm : Type where
| var : I -> Trm -- `x`
| val : Val → Trm -- AKA literal, `3`
-- TODO: how about typing evidence?
| subtypeEv: (tUnder: Typ) -> (tOver: Typ) -> Trm -- `Under <:< Over`
| apply : (fn: Trm) -> (arg: Trm) -> Trm -- this should need a subtypeEv

end

namespace postpone

inductive TypCtor : Type where -- type constructor! not type! not in core DOT!
| ctor: (arg : I -> Typ I) -> TypCtor

end postpone

end Syntax

end Dot
