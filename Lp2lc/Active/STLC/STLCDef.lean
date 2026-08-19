import Std
import «Lp2lc».Active.Util

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/--
Evidence that a binder carrier [C] extends the enclosing carrier [E]:

the evidence is the coercion embedding references to enclosing binders into
[C], so lambda bodies can capture their environment while remaining
covariant in [C].
-/
abbrev Greater (C E : UIdU) := Coe E C

/--
Source type syntax.

`primitive` classifies primitive bytecode values and `fn` classifies functions.
-/
inductive AST : Parameters → Label → Type 2 where
| primitive : AST F .typ -- `AnyVal` in Scala, accepts only primitive values
| fn (tIn : AST F .typ) (tOut : AST F .typ) : AST F .typ -- function
/--
Source term syntax.

Primitive value terms are self-typed, while function values carry their input
type. Applications and references are unannotated.

In HOAS there is no syntax-level context binding terms to types, so function
input annotations are the extrinsic typing evidence available to the compiler.
They are not intrinsic typing indices on terms.
-/
| val (v : AST F .val) : AST F .trm -- AKA literal
| apply (fn : AST F .trm) (arg : AST F .trm) : AST F .trm -- fn must be a function that can be applied on arg
| ref (s : F.C) : AST F .trm -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala), Evidence is required to proof that `x` is a valid index in the variable context
/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Function values carry their input type so the compiler can type-check HOAS bodies.
-/
| lit (repr : F.D) : AST F .val -- most specific type is always `primitive`
/--
Binds over a carrier-parametric argument so `AST` remains covariant in its carrier.

The body result is carried over [C] and [Greater C F.C] is required as evidence
that enclosing binders can be embedded into [C]; without it every binder
introduces a fresh carrier and closures cannot be expressed.
-/
| lam (body : {C : UIdU} → [s : Greater C F.C] → (arg : C) → AST { C := C, D := F.D } .trm) (tIn : AST F .typ) : AST F .val -- most specific type is always `.fn tIn _`

section variable {P : Parameters}

namespace AST

abbrev Typ (F : Parameters) := AST F .typ
abbrev Trm (F : Parameters) := AST F .trm
abbrev Val (F : Parameters) := AST F .val

section variable (F : Parameters)

-- structure Trm2Typ where -- TODO: cleanup, inferering with recarrier
--   trm : Trm F
--   typ : Typ F

-- structure Trm2Val where
--   trm : Trm F
--   val : Val F

end

/--
Rebuilds syntax over a different group of parameters along a carrier map.

References are transported along the map while binders pass through
unchanged, making `AST` covariant w.r.t both [Parameters.C] and [Parameters.D]
-/
def map {F G : Parameters} (mC : F.C → G.C) (mD : F.D → G.D)
    {l : Label} (self : AST F l) : AST G l :=
  match self with
  | .primitive => .primitive
  | .fn tIn tOut => .fn (tIn.map mC mD) (tOut.map mC mD)
  | .val v => .val (v.map mC mD)
  | .apply fnTerm arg => .apply (fnTerm.map mC mD) (arg.map mC mD)
  | .ref s => .ref (mC s)
  | .lit repr => .lit (mD repr)
  | .lam body tIn =>
      let body' : {C : UIdU} → [sG : Greater C G.C] → C → AST { C := C, D := G.D } .trm :=
        λ {C} [sG : Greater C G.C] (arg : C) =>
          (body (s := ⟨λ f => sG.coe (mC f)⟩) arg).map
            (F := { C := C, D := F.D }) (G := { C := C, D := G.D })
            (λ c => c) mD
      .lam body' (tIn.map mC mD)

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

/-- Owns the runtime receipt bridge for executable STLC values. -/
class ExeEnv extends HasData where
  mkUId4Val : CanMkUIdFor (λ T => AST.Val { C := T, D := D })

namespace ExeEnv
section variable (env : ExeEnv)

abbrev trm2valCtx : Fixpoint (λ T => AST.Val { C := T, D := env.D }) := env.mkUId4Val.mkEquiv

abbrev ExeParameters : Parameters := { C := env.trm2valCtx.UId, D := env.D }

end
end ExeEnv

namespace AST

/-- Evaluates terms whose references carry receipts from the runtime context. -/
def eval [env : ExeEnv]
    (self : Trm env.ExeParameters) : RecOpt (Val env.ExeParameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      let anf := (eval fnTerm fuel, eval arg fuel)
      match anf with
      | (.yield (some (.lam body _tIn)), .yield (some input)) =>
        let receipt := env.trm2valCtx.inv input
        eval (body (s := ⟨id⟩) receipt) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref receipt =>
      .yield (some (env.trm2valCtx.get receipt))

end AST

end

end Lp2lc.Active.STLC
