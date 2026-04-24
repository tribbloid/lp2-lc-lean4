import Std

import Aesop
import «Lp2lc».Active.Util

namespace Lp2lc.Active.DOT

open Util

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

inductive Evidence : Type where -- a thin wrapper of 2 "Typ", there is no co/contravariant evidence, which is just a function between 2 subtypeEv
-- TODO: dependent subtypeEv? then maybe it can be merged into depFn?
| subtypeEv (tUnder: Typ) (tOver: Typ) : Evidence -- subtype evidence, AKA coercion, `Under <:< Over`, notice that co/contravariance evidence are just higher-kind subtype evidence: `K[-T]` means `(X <:< Y) <:< (K[Y] <:< K[X])`
| congruenceEv (tL: Typ) (tR: Typ) : Evidence -- congruence evidence, if `L === R` then all their inhabitats are equal (namely `∀ (l: L, r: R), l.T =:= r.T`), not in core DOT but a critical improvement.

inductive Typ : Type where
-- | later (raw: Typ) : Typ -- don't know how to use it in iris yet.
| primitive : Typ -- `AnyVal`, won't differentiate Int/Float/Byte.
| evidence (ev: Evidence) : Typ -- ev can be both type & value
| depFn (tIn : Typ) (tOut: (arg: I) -> Typ) : Typ -- function `In => Out` or dependent function (if "tOut" uses "arg")
| oneMember (_ : MemberDeclaration) : Typ -- AKA object1, record1, 1 member only
| depSelectTyp (base: Trm) (tK: Name) : Typ -- `base.K`
-- TODO: this "body" definition assumes polymorphic output schema depending on input, is it true?
| selfBinder (body: (this: I) -> Typ) : Typ -- AKA Mu-type, body can refer to `this` (If de Bruijn serial is used instead of PHOAS, `this` would have serial "0")
| singleton (v: Trm) : Typ -- path singleton type, v can only be a "var" (`x.type`) or "depSelectTrm" (`x.name.type`), otherwise compilation fail
| and (tX: Typ) (tY: Typ) : Typ -- AKA intersection, `X & Y`
| or (tX: Typ) (tY: Typ) : Typ -- AKA union, `X | Y`
| top  : Typ -- `Any`
| bottom  : Typ -- `Nothing`
-- below are not part of core DOT
-- | genericApply (ctor: TypCtor) (arg: TypCtor): Typ

inductive MemberDeclaration: Type where -- member of an object/record, this is only the type-level declaration, not definition/implementation
| typeAlias (tName: Name) : MemberDeclaration -- `{type Name}`, it deliberately contain no type assigment or bound, they are evidence terms in the same object
| term (name: Option Name) (isImplicit: Bool) (annotation: Typ) : MemberDeclaration -- `{term name = Tm}`, they are multi-indexed after compilation: by name (if name exists) and by "tUnder" (if "isGiven" and is a "subtypeEv"")

structure ObjectBody where
  lookup : Name → Option MemberDeclaration

inductive Trm : Type where -- AKA expression, expr
| var (symbol: I) (tOver: Typ) : Trm -- variable, `x`, almost always bounded & never free (In PHOAS it is imposible to construct wildcard "(symbol: I)"), `tOver` is the upper-bound of "x"
| val (v : Val) : Trm -- value, AKA literal
| depSelectTrm (base: Trm) (name: Name) : Trm  -- `object.name`
| depApply (fn: Trm) (arg: Trm) : Trm -- application of (dependent?) function, execution requires constructing subtyping lattice from AST (which contains many "Evidence")

-- { theoretically everything in this section should have type erased to be used in runtime, but this is not enforced
inductive Val : Type where -- evaluation results and args of Atomic Normal Form (ANF), `Typ` CANNOT be carried! they are erased at runtime!
| primitive (repr: ByteCode) : Val -- `3`, `3.2`, `true` etc. Type is always ".primitive"
| evidence (ev: Evidence) : Val -- ev can be both type & value
-- TODO: does it really need a body? Why can't it be merged into subtypeEv ?
| depFn (body : (arg: I) -> Trm) : Val -- see "Typ.depFn"
| object (body : (this: I) -> ObjectBody) : Val -- object/record with a member lookup that can refer to `this`, DOT only uses structural typing so Trait has to carry an extra hidden type member
-- }

inductive TypCtor : Type where -- type constructor! not type! not in core DOT!
| tVar (symbol: I): TypCtor
| ctor (body: ((arg : I) -> TypCtor)): TypCtor
-- | higherCtor (body: (arg: I) -> TypCtor) : TypCtor
| apply (ctor: TypCtor) (arg: TypCtor): TypCtor

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
