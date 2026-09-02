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

In HOAS there is no syntax-level context binding terms to types, so function
input annotations are the extrinsic typing evidence available to the compiler.
They are not intrinsic typing indices on terms.
-/
| val (v : AST P .val) : AST P .trm -- AKA literal
| apply (fn : AST P .trm) (arg : AST P .trm) : AST P .trm -- fn must be a function that can be applied on arg
| ref (receipt : P.C) : AST P .trm -- reference, AKA variable/var (I don't like this name as it implies mutability in Scala)
/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Function values carry their input type so the compiler can type-check HOAS bodies.
-/
| lit (repr : P.D) : AST P .val -- most specific type is always `primitive`
/-
TODO: In my previous attempt to make AST.lam PHOAS definition covariant, I accidentally introduced a vulnerability to define exotic term:

the current lambda body can be defined to produce different AST based on arg type, breaking its parametricity

The single-carrier migration keeps this callback intentionally unchecked. Although
the argument is certified by `{x : C // ev x}`, proof irrelevance does not erase
`x.val`; the binder-identity regression therefore remains the explicit witness for
this unresolved soundness issue.
-/
/--
Binds a phase-certified receipt over the shared [P.C] carrier.

The callback is intentionally unchecked: it may inspect the underlying receipt,
so this representation does not by itself guarantee relational parametricity.
-/
| lam (body : {ev : P.C → Prop} → (arg : {uid : P.C // ev uid}) → AST P .trm)
    (tIn : AST P .typ) : AST P .val -- most specific type is always `.fn tIn _`

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



/--
Shares one receipt carrier between executable values and build-time types.

The underlying view stores a tagged value-or-type payload. Runtime and build
contexts refine that view independently through [UIdEquiv.Lesser]. The subtype
proof certifies which payload is available, but the unchecked lambda callback
can still inspect its underlying receipt; no soundness claim is made here.
-/
class TypOrValRefs extends HasData where --FIXME: rename to ValOrTypRefs
  uid2either : UIdView (λ T =>
    let P : Parameters := { C := T, D := D }

    AST.Val P ⊕ AST.Typ P
  )

namespace TypOrValRefs
section variable (self : TypOrValRefs)

/-- The shared syntax parameters are fixed by the mixed receipt view. -/
abbrev Parameters : Parameters := { C := self.uid2either.UId, D := self.D }

end
end TypOrValRefs

/-- Owns the runtime receipt bridge for executable STLC values. -/
class ExeEnv (refs : TypOrValRefs) where
  uid2valCtx : UIdEquiv.Lesser (base := refs.uid2either)
    (Sum.inl : AST.Val refs.Parameters →
      AST.Val refs.Parameters ⊕ AST.Typ refs.Parameters)

namespace AST

/-- Evaluates executable terms whose references carry receipts from the runtime context. -/
def eval [refs : TypOrValRefs] [env : ExeEnv refs]
    (self : Trm refs.Parameters) : RecOpt (Val refs.Parameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      let anf := (eval fnTerm fuel, eval arg fuel)
      match anf with
      | (.yield (some (.lam body _tIn)), .yield (some input)) =>
        let receipt := env.uid2valCtx.inv input
        eval (body receipt) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref receipt =>
      match refs.uid2either.get receipt with
      | .inl value => .yield (some value)
      | .inr _typ => .yield none

end AST

end

end Lp2lc.Active.STLC
