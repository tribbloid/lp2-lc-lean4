import Std

import Aesop
import «Lp2lc».Active.DOT.Util

namespace Lp2lc.Active.DOT

/-
here is the self-contained syntax for the latest DOT (System D-Diamond with
object/record, with real ∀).

It is:

- Not System F! (or its extension, lack of explicit polyFn, polyArrow, fake ∀)
- Not WadlerFest 2016 version! (lack of union type)
-/



section Syntax

variable (I: Type)[DecidableEq I] -- index

mutual

inductive Entry: Type where -- member of an object/record
| typeAlias (tLabel: Label) : Entry -- `{type Label}`, it deliberately contain no type assigment or bound, they are evidence-only terms in the same object ("subtypeEv" only in DOT but will include "co/contravarianceEv" later).
| term (label: Label) (tm: Trm) : Entry -- `{term label = Tm}`

inductive Typ : Type where
-- | later (raw: Typ) : Typ -- don't know how to use it in iris yet.
| primitive : Typ -- `AnyVal`, won't differentiate Int/Float/Byte.
| depFn (tIn : Typ) (tOut: (arg: I) -> Typ) : Typ -- function `In => Out` or dependent function (if "tOut" uses "arg")
| subtypeEv (tUnder: Typ) (tOver: Typ) : Typ -- subtype evidence, AKA coercion, `Under <:< Over`
| entry (single : Entry) : Typ -- AKA object1, record1, 1 member only
| depSelectTyp (base: Trm) (tK: Label) : Typ -- `base.K`
| selfBinder (body: (arg: I) -> Typ) : Typ -- AKA Mu-type, the delimiter/wrapper in an AST of which "Trm.self" refers to
| singleton (v: Trm) : Typ -- path singleton type that can only bind `v`, `v.type`
| and (tX: Typ) (tY: Typ) : Typ -- AKA intersection, `X & Y`
| or (tX: Typ) (tY: Typ) : Typ -- AKA union, `X | Y`
| top  : Typ -- `Any`
| bottom  : Typ -- `Nothing`

inductive Val : Type where -- evaluation results and args of Atomic Normal Form (ANF), `Typ` CANNOT be carried! they are erased at runtime!
| primitive : Val -- `3`, `3.2`, `true` etc.
| object (lookup : ObjectBody Entry) : Val -- carrying a member lookup, DOT only uses structural typing so Trait has to carry an extra hidden type member
| depFn (body : (arg: I) -> Trm) : Val -- see "Typ.depFn", does it really need a body?
| subtypeEv : Val -- see "Typ.subtypeEv", has no body, erased at runtime

inductive Trm : Type where -- AKA expression, unlike Val, it is indexed by type
| var (symbol: I) : Trm -- variable, `x`, always bounded, almost always locally closed (In PHOAS it is imposible to construct wildcard "(symbol: I)")
| val (v : Val) : Trm -- value, AKA literal
| self : Trm -- self-var, `this`, must be inside a "Typ.selfBinder". If de Bruijn serial is used for bounded var then this is the "0".
| depSelectTrm (base: Trm) (label: Label) : Trm  -- `object.label`
| depApply (fn: Trm) (arg: Trm) : Trm -- application of (dependent?) function

-- TODO: some of these can be merged actually, e.g. subtypeEv and depFn

end

namespace postpone -- DOT with type constructors/generics with type bound & variance, fully defined Scala.
-- TODO: eventually this part has to be added with examples, including
-- elaborator rules

inductive TypCtor : Type where -- type constructor! not type! not in core DOT!
| ctor: (arg : I -> Typ I) -> TypCtor

end postpone

/-
Semantics
TODO: each constraint has 2 semantic representation:

- embedded/definitional: type bindings are predicates for terms (Trm -> Prop), subtype
  evidences are higher-order predicates:
  ∀ {T1 T2 : Trm -> Prop} {v : Trm} (ev: T1 <:< T2) (T1 v) -> (T2 v)
- explicit/operational: type bindings are lookup, subtype evidences are lattice, both forms
  the Env/Context

they don't have to match, but which one would you choose?
-/

/-
if choosing embedded/definitional:

Some Val should be indistinguisable from denotation, (all of them if positivity
doesn't block it), can we avoid repetitive definitions?
-/

-- inductive Data: Type where -- AKA Denotation
-- | primitive : Data -- `3`, `3.2`, `true` etc.
-- | object : (Lookup Data or (Data -> Data) ) → Data -- carrying a member lookup, in DOT objects are only identified only by structure, Trait has to carry a hidden type member



end Syntax

abbrev TermClosed := {I : Type} -> Trm I

end DOT
