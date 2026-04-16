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
  - Explicit Env/Context/Store is just a collection of all 3 evidences. It's
    only an IR built from each AST tree and nothing else, but it's an important
    one. Without it we may never be able to infer the equality of
    - `type A; type B <: A` and
    - `type B; type A >: B`
-/

def ByteCode := String

section Syntax

variable (I: Type)[DecidableEq I][BEq I][Hashable I] -- index
mutual

inductive Entry: Type where
| type: I -> Ty -> Entry
| term: I -> Tm -> Entry
deriving DecidableEq, Repr

inductive Ty : Type where
| primitive : Ty -- `AnyVal`, won't differentiate Int/Float/Byte.
| fn : (tIn :Ty) -> (tOut: Ty) -> Ty -- function, `In => Out`
| object  : Entry → Ty
| selection: Ty
| and: (tX: Ty) -> (tY: Ty) -> Ty -- AKA intersection, `X & Y`
| or: (tX: Ty) -> (tY: Ty) -> Ty -- AKA union, `X | Y`
| top  : Ty -- `Any`
| bottom  : Ty -- `Nothing`
deriving DecidableEq, Repr

inductive Tm : Type where
| var : I -> Tm -- `x`
| literal : ByteCode -> Tm -- `3`
-- TODO: how about typing evidence?
| subtypeEv: (tUnder: Ty) -> (tOver: Ty) -> Tm -- `Under <:< Over`
| apply : Tm -> Tm -> Tm -- this should need a subtypeEv
| fn : (arg : I -> Tm) -> Tm
deriving DecidableEq, Repr

end

namespace postpone

inductive TyCtor : Type where -- type constructor! not type! not in core DOT!
| ctor: (arg : I ->  Ty) -> TyCtor
deriving DecidableEq, Repr

end postpone

end Syntax

end Dot
