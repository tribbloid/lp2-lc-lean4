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
- We haven't reach variance yet, so both Function and SubtypeEvidence are
  invariant (IRL they are 1-contravariant and 2-covariant, but we will get
  there)
- Type erasure: Val do NOT carry any type information
- Currying is always enabled, a binary operation is fold into curried form of 2
  unary operations.
-/

def ByteCode := String

abbrev Label := String

abbrev LookupFn (V : Type) := Label → Option V

section

variable (V : Type)

namespace LookupFn

def empty : LookupFn V := fun _ => none

def set (σ : LookupFn V) (x : Label) (v : V) : LookupFn V :=
  fun y => if y = x then some v else σ y

@[simp] theorem set_same (σ : LookupFn V) (x : Label) (v : V) :
  LookupFn.set (V := V) σ x v x = some v := by
  simp [LookupFn.set]

@[simp] theorem set_other (σ : LookupFn V) (x y : Label) (v : V) (h : y ≠ x) :
  LookupFn.set (V := V) σ x v y = σ y := by
  simp [LookupFn.set, h]

end LookupFn

structure ObjectBody (V : Type) where
  underlying : Label → Option V


end

section Syntax

variable (I: Type)[DecidableEq I] -- index

mutual

inductive Entry: Type where -- member of an object
| type (tLabel: Label) (ty: Typ) : Entry -- `{type Label = Ty}`
| term (label: Label) (tm: Trm) : Entry -- `{term label = Tm}`

inductive Typ : Type where
-- | later (raw: Typ) : Typ -- don't know how to use it in iris yet.
| primitive : Typ -- `AnyVal`, won't differentiate Int/Float/Byte.
| subtypeEv (tUnder: Typ) (tOver: Typ) : Typ -- subtype evidence, AKA coercion, `Under <:< Over`
| depFn (tIn : Typ) (tOut: Typ) : Typ -- function (`In => Out`) or dependent function (if `tOut` is a "depSelectTyp")
| object1 (entry : Entry) : Typ -- AKA record1, only has 1 member
 -- TODO: this hasn't been defined in PHOAS before, need to double check.
| depSelectTyp (object: I) (tLabel: Label) : Typ -- `object.Label`
| self (self: Typ) : Typ -- AKA type binding, Mu-type, `this`
| and (tX: Typ) (tY: Typ) : Typ -- AKA intersection, `X & Y`
| or (tX: Typ) (tY: Typ) : Typ -- AKA union, `X | Y`
| top  : Typ -- `Any`
| bottom  : Typ -- `Nothing`

inductive Val : Type where -- evaluation results and args of Atomic Normal Form (ANF), `Typ` CANNOT be carried! they are erased at runtime!
| primitive : Val -- `3`, `3.2`, `true` etc.
| object (lookup : ObjectBody Entry) : Val -- carrying a member lookup, in DOT objects are only identified only by structure, Trait has to carry a hidden type member
| depFn (body : (arg: I) -> Trm) : Val -- same as Typ
-- TODO: do we need typing evidence?
-- TODO: for operational semantics, Val should be indistinguisable from denotation, in the next version they should be unified (if positivity doesn't block it)

inductive Trm : Type where -- AKA expression, unlike Val, it is indexed by type
| var (symbol: I) : Trm -- `x`
| val (v : Val) : Trm -- AKA literal, Values are terms
| depSelectTrm (object: I) (label: Label) : Trm  -- `object.label`
| depApply (fn: Trm) (arg: Trm) : Trm -- application of (dependent?) function
| subtypeEv : Trm -- same as Typ, has no coercion body, erased at runtime

end

-- inductive Data: Type where -- AKA Denotation
-- | primitive : Data -- `3`, `3.2`, `true` etc.
-- | object : (Lookup Data or (Data -> Data) ) → Data -- carrying a member lookup, in DOT objects are only identified only by structure, Trait has to carry a hidden type member


namespace postpone

inductive TypCtor : Type where -- type constructor! not type! not in core DOT!
| ctor: (arg : I -> Typ I) -> TypCtor

end postpone

end Syntax

end Dot
