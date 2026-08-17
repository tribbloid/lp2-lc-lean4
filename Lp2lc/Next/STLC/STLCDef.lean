import Std
import «Lp2lc».Next.Util

namespace Lp2lc.Next.STLC

open Lp2lc.Next.Util
open Lp2lc.Active.Util

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
/-- Binds over a carrier-parametric argument so `AST` remains covariant in its carrier. -/
| lam (body : {C : UIdU} → (arg : C) → AST { C := C, D := F.D } .trm) (tIn : AST F .typ) : AST F .val -- most specific type is always `.fn tIn _`

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
Rebuilds syntax over another carrier along a carrier map.

References are transported along the map while binders pass through
unchanged, making `AST` covariant in its carrier.
-/
def map (F G : Parameters) (mC : F.C → G.C) (mD : F.D → G.D) -- TODO: `F G` should be implicit
    {l : Label} (self : AST F l) : AST G l :=
  match self with
  | .primitive => .primitive
  | .fn tIn tOut => .fn (tIn.map F G mC mD) (tOut.map F G mC mD)
  | .val v => .val (v.map F G mC mD)
  | .apply fnTerm arg => .apply (fnTerm.map F G mC mD) (arg.map F G mC mD)
  | .ref s => .ref (mC s)
  | .lit repr => .lit (mD repr)
  | .lam body tIn =>
      let body' : {C : UIdU} → C → AST { C := C, D := G.D } .trm :=
        λ {C} (arg : C) =>
          (body arg).map { C := C, D := F.D } { C := C, D := G.D }
            (λ c => c) mD
      .lam body' (tIn.map F G mC mD)

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

open Lp2lc.Next.Util.Free (Fixpoint FixpointCtor)

namespace ExeEnv

end ExeEnv

/-- Owns the bridge constructor shared by concrete STLC contexts. -/
class ExeEnv extends FixpointCtor where
  D : DataU

namespace ExeEnv
section variable (env : ExeEnv)

def trm2valCtx :=
  env.mkFixpoint (λ T => AST.Val { C := T, D := env.D })

abbrev ExeParameters : Parameters :=
  { C := env.trm2valCtx.UId, D := env.D }

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
        eval (body receipt) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref receipt =>
      .yield (some (env.trm2valCtx.get receipt))

end AST

/-- Adds the compile-time typing context to an execution environment. -/
class BuildEnv extends ExeEnv

namespace BuildEnv
section variable (env : BuildEnv)

def trm2typCtx :=
  env.mkFixpoint (λ T =>
    let TC := env.trm2valCtx.UId ⊕ T
    AST.Val { C := TC, D := env.D })

abbrev BuildParameters : Parameters :=
  { C := env.trm2valCtx.UId ⊕ env.trm2typCtx.UId, D := env.D }

end
end BuildEnv

end

end Lp2lc.Next.STLC
