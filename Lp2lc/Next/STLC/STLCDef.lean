import Std
import «Lp2lc».Next.Util

namespace Lp2lc.Next.STLC

open Lp2lc.Next.Util
open Lp2lc.Active.Util

section variable {F : Free}

/--
Source type syntax.

`primitive` classifies primitive bytecode values and `fn` classifies functions.
-/
inductive AST (F : Free) : Label → Type where
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
| ref (s : F.Carrier) : AST F .trm -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala), Evidence is required to proof that `x` is a valid index in the variable context
/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Function values carry their input type so the compiler can type-check HOAS bodies.
-/
| lit (repr : F.Data) : AST F .val -- most specific type is always `primitive`
| lam (body : (arg : F.Carrier) → AST F .trm) (tIn : AST F .typ) : AST F .val -- most specific type is always `.fn tIn _`

namespace AST

abbrev Typ (F : Free) := AST F .typ
abbrev Trm (F : Free) := AST F .trm
abbrev Val (F : Free) := AST F .val

section variable (F : Free)

-- structure Trm2Typ where -- TODO: cleanup, inferering with recarrier
--   trm : Trm F
--   typ : Typ F

-- structure Trm2Val where
--   trm : Trm F
--   val : Val F

end


namespace Source

abbrev Typ (Data : DataU) :=
  ∀ Carrier : UIdU, AST.Typ (Free.mk Carrier Data)

abbrev Trm (Data : DataU) :=
  ∀ Carrier : UIdU, AST.Trm (Free.mk Carrier Data)

abbrev Val (Data : DataU) :=
  ∀ Carrier : UIdU, AST.Val (Free.mk Carrier Data)

end Source

namespace Typ

/-- Rebuilds type syntax over another carrier without converting terms or binders. -/
def recarrier {Source Target : Free} (self : AST.Typ Source) : AST.Typ Target :=
  match self with
  | .primitive => .primitive
  | .fn tIn tOut => .fn (recarrier tIn) (recarrier tOut)

end Typ

namespace Val

def asTrm (self : AST.Val F) : AST.Trm F := .val self

end Val

end AST

open AST

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE : LE (AST.Typ F) := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
@[instance_reducible]
instance typDecidableLE : DecidableLE (AST.Typ F)
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
class ExeEnv where
  F : Free
  ctor : FixpointCtor F

namespace ExeEnv

def trm2valCtx (env : ExeEnv) : Fixpoint env.F AST.Val :=
  @FixpointCtor.mkFixpoint env.F env.ctor AST.Val

abbrev CVar (env : ExeEnv) : Free :=
  { env.F with Carrier := env.trm2valCtx.UId }

end ExeEnv

/-- Adds the compile-time typing context to an execution environment. -/
class BuildEnv extends ExeEnv

namespace BuildEnv

def trm2typCtx (env : BuildEnv) : Fixpoint env.F AST.Typ :=
  @FixpointCtor.mkFixpoint env.F env.ctor AST.Typ

abbrev CTyp (env : BuildEnv) : Free :=
  { env.F with Carrier := env.trm2typCtx.UId }

end BuildEnv

end

end Lp2lc.Next.STLC
