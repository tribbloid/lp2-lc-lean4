import Std
import «Lp2lc».Active.Util

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

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
    (body : AST { P with B := P.B ⊕ Unit } .trm)
    (tIn : AST P .typ) :
    AST P .val -- most specific type is always `.fn tIn _`

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

/-- Rebuilds syntax while classifying source binders as target free or bound references. -/
@[simp]
def recarrier {P Q : Parameters} {l : Label} (self : AST P l)
    (mF : P.F → Q.F) (mB : P.B → Q.F ⊕ Q.B) (mD : P.D → Q.D) : AST Q l :=
  match self with
  | .primitive => .primitive
  | .fn tIn tOut => .fn (tIn.recarrier mF mB mD) (tOut.recarrier mF mB mD)
  | .val value => .val (value.recarrier mF mB mD)
  | .apply fnTerm arg => .apply (fnTerm.recarrier mF mB mD) (arg.recarrier mF mB mD)
  | .ref (.inl free) => .ref (.inl (mF free))
  | .ref (.inr bound) => .ref (mB bound)
  | .lit repr => .lit (mD repr)
  | .lam body tIn =>
    .lam
      (body.recarrier mF
        (λ bound =>
          match bound with
          | .inl outer =>
            match mB outer with
            | .inl free => .inl free
            | .inr target => .inr (.inl target)
          | .inr () => .inr (.inr ()))
        mD)
      (tIn.recarrier mF mB mD)

/-- Replaces the newest structural lambda slot while preserving outer binders. -/
@[simp]
def instantiateLamBody {P : Parameters}
    (self : AST { P with B := P.B ⊕ Unit } .trm) (arg : P.B) : AST P .trm :=
  self.recarrier
    (id : P.F → P.F)
    (λ bound =>
      match bound with
      | .inl outer => .inr outer
      | .inr () => .inr arg)
    (id : P.D → P.D)

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
        eval (body.instantiateLamBody receipt) fuel
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
