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
FIXME: Switch to certified AST

The callback's `arg.val` always has type `P.C`, but `.ref arg.val` stores only that
raw receipt and erases `arg.property : ev arg.val`. Runtime and build contexts can
mint different `P.C` receipts for corresponding binders, so an unchecked callback
can compare receipt identities and produce phase-dependent syntax. The
`binderIdentityCounterexample` demonstrates this mismatch: evaluation fails while
inference yields `.primitive`.

Under the PHOAS limitation, the shortest way to enable this is to attach a short certificate to the application result of AST.lam body during AST.eval,
indicating that all free variable (represented by AST.ref) in the AST have a value binding, this certificate is discarded during AST.infer,
which can handle both Val and Trm in it's recursive execution. At this point, AST.lam can revert to the original PHOAS definition,
and the predicate `{ev : P.C → Prop}` in AST.lam can be discarded.

It should be noted that de Bruijn serial or explicit substitution/recarrier of AST should be avoided at all cost, as they tend to bloat soundness proof
-/
/--
Binds a phase-certified receipt over the shared [P.C] carrier.

The carrier type is always [P.C]. The callback remains unchecked because it can
inspect raw receipt identity and construct `.ref arg.val`, which discards the
phase-specific `ev` evidence.
-/
| lam (body : {ev : P.C → Prop} → (arg : {uid : P.C // ev uid}) → AST P .trm)
    (tIn : AST P .typ) : AST P .val -- most specific type is always `.fn tIn _`

section variable {P : Parameters}

namespace AST

abbrev Typ (P : Parameters) := AST P .typ
abbrev Trm (P : Parameters) := AST P .trm
abbrev Val (P : Parameters) := AST P .val

section variable (P : Parameters)

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
proof certifies which payload is available, but [AST.ref] stores only the raw
receipt. Projecting a lambda argument to `.val` therefore discards that proof, so
this infrastructure alone does not prevent phase-dependent lambda bodies.
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
