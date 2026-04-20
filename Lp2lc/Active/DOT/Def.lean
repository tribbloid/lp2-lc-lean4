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
-- TODO: this huge block doesn't model type erasure, for that we need to define 2 blocks referring to runtime AST and compile-time AST respectively

inductive Entry: Type where -- member of an object/record, visible in both "Trm" and "Typ"
| term (label: Label) (tm: Trm) : Entry -- `{term label = Tm}`
| typeAlias (tLabel: Label) : Entry -- `{type Label}`, it deliberately contain no type assigment or bound, they are evidence-only terms in the same object ("subtypeEv" only in DOT but will include "co/contravarianceEv" later).
| ev (_ : Evidence) : Entry -- unlike term, evidence are nameless & multi-indexed by types

inductive Typ : Type where
-- | later (raw: Typ) : Typ -- don't know how to use it in iris yet.
| primitive : Typ -- `AnyVal`, won't differentiate Int/Float/Byte.
-- TODO: technically it is a non-depenent function, is this case necessary?
| subtypeEv (tUnder: Typ) (tOver: Typ) : Typ -- subtype evidence, AKA coercion, `Under <:< Over`
| depFn (tIn : Typ) (tOut: (arg: I) -> Typ) : Typ -- function `In => Out` or dependent function (if "tOut" uses "arg")
| entry (single : Entry) : Typ -- AKA object1, record1, 1 member only
| depSelectTyp (base: Trm) (tK: Label) : Typ -- `base.K`
-- TODO: this "body" definition assumes polymorphic output schema depending on input.
| selfBinder (body: (this: I) -> Typ) : Typ -- AKA Mu-type, body can refer to `this` (If de Bruijn serial is used instead of PHOAS, `this` would have serial "0")
| singleton (v: Trm) : Typ -- path singleton type that can only bind `v`, `v.type`
| and (tX: Typ) (tY: Typ) : Typ -- AKA intersection, `X & Y`
| or (tX: Typ) (tY: Typ) : Typ -- AKA union, `X | Y`
| top  : Typ -- `Any`
| bottom  : Typ -- `Nothing`
-- below are not part of core DOT
-- | genericApply (ctor: TypCtor) (arg: TypCtor): Typ

structure ObjectBody where
  underlying : Label → Option Entry

inductive Val : Type where -- evaluation results and args of Atomic Normal Form (ANF), `Typ` CANNOT be carried! they are erased at runtime!
| primitive (repr: ByteCode) : Val -- `3`, `3.2`, `true` etc.
-- TODO: does it really need a body? Why can't it be merged into subtypeEv ?
| depFn (body : (arg: I) -> Trm) : Val -- see "Typ.depFn"
| object (body : (this: I) -> ObjectBody) : Val -- object/record with a member lookup that can refer to `this`, DOT only uses structural typing so Trait has to carry an extra hidden type member

-- every under this line in "Syntax" can be annotated by type (intrinsic or extrinsic)

inductive Evidence: Type where
| subtypeEv : Evidence  -- see "Typ.subtypeEv", has no body, erased at runtime

inductive Trm : Type where -- AKA expression, unlike Val, it is indexed by type
| var (symbol: I) : Trm -- variable, `x`, always bounded, almost always locally closed (In PHOAS it is imposible to construct wildcard "(symbol: I)")
| val (v : Val) : Trm -- value, AKA literal
| evidence (_: Evidence) : Trm
| depSelectTrm (base: Trm) (label: Label) : Trm  -- `object.label`
| depApply (fn: Trm) (arg: Trm) : Trm -- application of (dependent?) function

inductive TypCtor : Type where -- type constructor! not type! not in core DOT!
| tVar (symbol: I): TypCtor
| ctor (body: ((arg : I) -> TypCtor)): TypCtor
-- | higherCtor (body: (arg: I) -> TypCtor) : TypCtor
| apply (ctor: TypCtor) (arg: TypCtor): TypCtor

obvious error

end


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

abbrev TrmClosed := {I : Type} -> Trm I

abbrev TypClosed := {I : Type} -> Typ I

end DOT
