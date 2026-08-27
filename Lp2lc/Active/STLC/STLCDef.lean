import Std
import «Lp2lc».Active.Util

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace AST

/-- Maps the free, bound, and data carriers of one syntax parameter set into another. -/
@[ext]
structure CarrierMap (P Q : Parameters) where
  mapF : P.F → Q.F
  mapB : P.B → Q.F ⊕ Q.B
  mapD : P.D → Q.D

namespace CarrierMap

/-- Leaves free and data carriers unchanged and keeps bound references bound. -/
def identity (P : Parameters) : CarrierMap P P where
  mapF := id
  mapB := Sum.inr
  mapD := id

/-- Applies a carrier map to a free-or-bound reference. -/
def mapRef {P Q : Parameters} (self : CarrierMap P Q) : P.F ⊕ P.B → Q.F ⊕ Q.B
  | .inl free => .inl (self.mapF free)
  | .inr bound => self.mapB bound

/-- Composes two carrier maps in source-to-target order. -/
def «then» {P Q R : Parameters} (self : CarrierMap P Q)
    (next : CarrierMap Q R) : CarrierMap P R where
  mapF := λ free => next.mapF (self.mapF free)
  mapB := λ bound => next.mapRef (self.mapB bound)
  mapD := λ repr => next.mapD (self.mapD repr)

/-- Extends a carrier map beneath one structural lambda binder. -/
def underBinder {P Q : Parameters} (self : CarrierMap P Q) :
    CarrierMap { P with B := P.B ⊕ Unit } { Q with B := Q.B ⊕ Unit } where
  mapF := self.mapF
  mapB
    | .inl outer =>
      match self.mapB outer with
      | .inl free => .inl free
      | .inr target => .inr (.inl target)
    | .inr () => .inr (.inr ())
  mapD := self.mapD

/-- Replaces the newest structural slot while mapping all outer carriers. -/
def bind {P Q : Parameters} (self : CarrierMap P Q) (arg : Q.F ⊕ Q.B) :
    CarrierMap { P with B := P.B ⊕ Unit } Q where
  mapF := self.mapF
  mapB
    | .inl outer => self.mapB outer
    | .inr () => arg
  mapD := self.mapD

@[simp]
theorem underBinderThen {P Q R : Parameters} (first : CarrierMap P Q)
    (second : CarrierMap Q R) :
    first.underBinder.«then» second.underBinder = (first.«then» second).underBinder := by
  ext value
  · rfl
  · cases value with
    | inl outer =>
      cases hFirst : first.mapB outer with
      | inl free => simp [«then», mapRef, underBinder, hFirst]
      | inr target =>
        cases hSecond : second.mapB target <;>
          simp [«then», mapRef, underBinder, hFirst, hSecond]
    | inr newest => cases newest; simp [«then», mapRef, underBinder]
  · rfl

end CarrierMap
end AST

mutual

/-- Source type syntax.

`primitive` classifies primitive bytecode values and `fn` classifies functions.
-/
inductive AST : Parameters → Label → Type 2 where
| primitive : AST P .typ -- `AnyVal` in Scala, accepts only primitive values
| fn (tIn : AST P .typ) (tOut : AST P .typ) : AST P .typ -- function
/--
Source term syntax.

Primitive value terms are self-typed, while function values carry their input
type. Applications and references are unannotated.

Terms are not intrinsically indexed by object-language types, so function input
annotations are the extrinsic typing evidence available to the compiler.
-/
| val (v : AST P .val) : AST P .trm -- AKA literal
| apply (fn : AST P .trm) (arg : AST P .trm) : AST P .trm -- fn must be a function that can be applied on arg
| ref (s : P.F ⊕ P.B) : AST P .trm -- free (.inl) or lambda-bound (.inr) reference, AKA variable/var (I don't like this name as it implies mutability in Scala)
/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Function values carry their input type so the compiler can type-check their bodies.
-/
| lit (repr : P.D) : AST P .val -- most specific type is always `primitive`
/-- Binds one fresh structural slot, after the outer [P.B] binder carrier. -/
| lam
    (body : LamBody P)
    (tIn : AST P .typ) :
    AST P .val -- most specific type is always `.fn tIn _`

/-- First-order syntax for a lambda body with one distinguished newest binder slot. -/
inductive LamBody : Parameters → Type 2 where
| mk (body : AST { P with B := P.B ⊕ Unit } .trm) : LamBody P

end

section variable {P : Parameters}

namespace AST

abbrev Typ (P : Parameters) := AST P .typ
abbrev Trm (P : Parameters) := AST P .trm
abbrev Val (P : Parameters) := AST P .val

section variable (P : Parameters)

-- structure Trm2Typ where -- TODO: cleanup, inferering with recarrier
--   trm : Trm P
--   typ : Typ P

-- structure Trm2Val where
--   trm : Trm P
--   val : Val P

end

-- TOOD: remove & don't use it, we don't need general upcast for AST.
-- def map {B : UIdU} {PF QF : UIdU} {PD QD : DataU} {l : Label}
--     (self : AST { F := PF, B := B, D := PD } l)
--     (mF : PF → QF) (mD : PD → QD) :
--     AST { F := QF, B := B, D := QD } l :=
--   match self with
--   | .primitive => .primitive
--   | .fn tIn tOut => .fn (tIn.map mF mD) (tOut.map mF mD)
--   | .val v => .val (v.map mF mD)
--   | .apply fnTerm arg => .apply (fnTerm.map mF mD) (arg.map mF mD)
--   | .ref (.inl f) => .ref (.inl (mF f))
--   | .ref (.inr b) => .ref (.inr b)
--   | .lit repr => .lit (mD repr)
--   | .lam body tIn => .lam (λ arg => (body arg).map mF mD) (tIn.map mF mD)

end AST

namespace LamBody

/-- Exposes the structural syntax stored by a lambda body. -/
def body {P : Parameters} (self : LamBody P) :
    AST { P with B := P.B ⊕ Unit } .trm :=
  match self with
  | .mk body => body

end LamBody

mutual

  /-- Rebuilds syntax while classifying source binders as target free or bound references. -/
  @[simp]
  def AST.recarrier {P Q : Parameters} {l : Label} (self : AST P l)
      (map : AST.CarrierMap P Q) : AST Q l :=
    match self with
    | .primitive => .primitive
    | .fn tIn tOut => .fn (tIn.recarrier map) (tOut.recarrier map)
    | .val value => .val (value.recarrier map)
    | .apply fnTerm arg => .apply (fnTerm.recarrier map) (arg.recarrier map)
    | .ref source => .ref (map.mapRef source)
    | .lit repr => .lit (map.mapD repr)
    | .lam body tIn => .lam (body.recarrier map) (tIn.recarrier map)

  /-- Rebuilds a structural lambda body beneath a carrier map. -/
  @[simp]
  def LamBody.recarrier {P Q : Parameters} (self : LamBody P)
      (map : AST.CarrierMap P Q) : LamBody Q :=
    match self with
    | .mk body => .mk (body.recarrier map.underBinder)

end

/-- Consecutive carrier changes are equivalent to their bundled composition. -/
@[simp]
theorem AST.recarrierComp {P Q R : Parameters} {l : Label} (self : AST P l)
    (first : AST.CarrierMap P Q) (second : AST.CarrierMap Q R) :
    (self.recarrier first).recarrier second = self.recarrier (first.«then» second) := by
  induction self using AST.rec
    (motive_2 := λ P body =>
      ∀ {Q R : Parameters} (first : AST.CarrierMap P Q) (second : AST.CarrierMap Q R),
        (body.recarrier first).recarrier second = body.recarrier (first.«then» second))
    generalizing Q R with
  | primitive => rfl
  | fn tIn tOut ihIn ihOut => simp [ihIn, ihOut]
  | val value ih => simp [ih]
  | apply fnTerm arg ihFn ihArg => simp [ihFn, ihArg]
  | ref source =>
    cases source with
    | inl free => rfl
    | inr bound =>
      cases hFirst : first.mapB bound <;> simp [AST.CarrierMap.«then»,
        AST.CarrierMap.mapRef, hFirst]
  | lit repr => rfl
  | lam body tIn ihBody ihIn => simp [ihBody, ihIn]
  | mk body ihBody =>
    simp only [LamBody.recarrier]
    rw [ihBody, AST.CarrierMap.underBinderThen]

/-- Consecutive carrier changes beneath a lambda preserve its newest binder slot. -/
@[simp]
theorem LamBody.recarrierComp {P Q R : Parameters} (self : LamBody P)
    (first : AST.CarrierMap P Q) (second : AST.CarrierMap Q R) :
    (self.recarrier first).recarrier second = self.recarrier (first.«then» second) := by
  cases self with
  | mk body =>
    simp only [LamBody.recarrier]
    rw [AST.recarrierComp, AST.CarrierMap.underBinderThen]

namespace LamBody

/-- Generates a body term by mapping outer carriers and replacing the newest slot. -/
def specialise {P Q : Parameters} (self : LamBody P) (map : AST.CarrierMap P Q)
    (arg : Q.F ⊕ Q.B) : AST Q .trm :=
  self.body.recarrier (map.bind arg)

/-- Generalized naturality of specialization under a subsequent carrier map. -/
def Conjecture {P : Parameters} (self : LamBody P) : Prop :=
  ∀ {Q R : Parameters} (first : AST.CarrierMap P Q) (second : AST.CarrierMap Q R)
    (arg : Q.F ⊕ Q.B),
    (self.specialise first arg).recarrier second =
      self.specialise (first.«then» second) (second.mapRef arg)

end LamBody

namespace AST

namespace Val

def asTrm (self : AST.Val P) : AST.Trm P := .val self

end Val

end AST

open AST

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE : LE (AST.Typ P) := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
@[instance_reducible]
instance typDecidableLE : DecidableLE (AST.Typ P)
  | .primitive, .primitive => isTrue rfl
  | .primitive, .fn _ _
  | .fn _ _, .primitive => isFalse (λ equality => nomatch equality)
  | .fn leftIn leftOut, .fn rightIn rightOut =>
    match typDecidableLE leftIn rightIn, typDecidableLE leftOut rightOut with
    | isTrue inputEqual, isTrue outputEqual => isTrue (inputEqual ▸ outputEqual ▸ rfl)
    | isFalse notEqual, _ => isFalse (λ equality => notEqual (AST.fn.inj equality).1)
    | _, isFalse notEqual => isFalse (λ equality => notEqual (AST.fn.inj equality).2)

class ExeRefs extends HasData where
  uid2val : UIdView (λ T => AST.Val { F := T, B := T, D := D })

namespace ExeRefs
section variable (self : ExeRefs)

abbrev ExeParameters : Parameters := { F := self.uid2val.UId, B := self.uid2val.UId, D := self.D }

end
end ExeRefs

/-- Owns the runtime receipt bridge for executable STLC values. -/
class ExeEnv (refs : ExeRefs) where
  uid2valCtx : UIdEquiv.Extendable.{3, 3} (base := refs.uid2val)

namespace AST

/-- Evaluates executable terms whose references carry receipts from the runtime context. -/
def eval [refs : ExeRefs] [env : ExeEnv refs]
    (self : Trm refs.ExeParameters) : RecOpt (Val refs.ExeParameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      let anf := (eval fnTerm fuel, eval arg fuel)
      match anf with
      | (.yield (some (.lam body _tIn)), .yield (some input)) =>
        let receipt := env.uid2valCtx.inv input
        eval (body.specialise (CarrierMap.identity _) (.inr receipt)) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref (.inl receipt) =>
      .yield (some (refs.uid2val.get receipt))
    | .ref (.inr receipt) =>
      .yield (some (refs.uid2val.get receipt))

end AST

end

end Lp2lc.Active.STLC
