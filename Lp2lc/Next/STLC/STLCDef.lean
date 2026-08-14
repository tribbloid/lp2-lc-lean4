import Std
import «Lp2lc».Next.Util

namespace Lp2lc.Next.STLC

open Lp2lc.Active.Util

section variable {F : Free}

inductive Label
| Typ
| Trm
| Val

/--
Source type syntax.

`primitive` classifies primitive bytecode values and `fn` classifies functions.
-/
inductive AST (F : Free) : Label → Type where
| primitive : AST F .Typ -- `AnyVal` in Scala, accepts only primitive values
| fn (tIn : AST F .Typ) (tOut : AST F .Typ) : AST F .Typ -- function
/--
Source term syntax.

Primitive value terms are self-typed, while function values carry their input
type. Applications and references are unannotated.

In HOAS there is no syntax-level context binding terms to types, so function
input annotations are the extrinsic typing evidence available to the compiler.
They are not intrinsic typing indices on terms.
-/
| val (v : AST F .Val) : AST F .Trm -- AKA literal
| apply (fn : AST F .Trm) (arg : AST F .Trm) : AST F .Trm -- fn must be a function that can be applied on arg
| ref (s : F.Carrier) : AST F .Trm -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala), Evidence is required to proof that `x` is a valid index in the variable context
/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Function values carry their input type so the compiler can type-check HOAS bodies.
-/
| lit (repr : F.Data) : AST F .Val -- most specific type is always `primitive`
| lam (body : (arg : F.Carrier) → AST F .Trm) (tIn : AST F .Typ) : AST F .Val -- most specific type is always `.fn tIn _`

namespace AST

abbrev Typ (F : Free) := AST F .Typ
abbrev Trm (F : Free) := AST F .Trm
abbrev Val (F : Free) := AST F .Val

section variable (F : Free)

structure Trm2Typ where
  trm : Trm F
  typ : Typ F

structure Trm2Val where
  trm : Trm F
  val : Val F

end


namespace Source

abbrev Typ (Data : TData) :=
  ∀ Carrier : TIndex, AST.Typ (Free.mk Carrier Data)

abbrev Trm (Data : TData) :=
  ∀ Carrier : TIndex, AST.Trm (Free.mk Carrier Data)

abbrev Val (Data : TData) :=
  ∀ Carrier : TIndex, AST.Val (Free.mk Carrier Data)

end Source

namespace Typ

/-- Rebuilds type syntax over another carrier without converting terms or binders. -/
def recarrier {Source Target : Free} (self : AST.Typ Source) : AST.Typ Target :=
  match self with
  | .primitive => .primitive
  | .fn tIn tOut => .fn (recarrier tIn) (recarrier tOut)

end Typ

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

open Lp2lc.Next.Util.Free (Fixpoint FixpointCtor WithEv)

/-- Owns the bridge constructor shared by concrete STLC contexts. -/
class ExeEnv (F : Free) where
  ctor : FixpointCtor F

namespace ExeEnv

def trm2valCtx {F : Free} (env : ExeEnv F) : Fixpoint F AST.Trm2Val :=
  @FixpointCtor.mkFixpoint F env.ctor AST.Trm2Val

abbrev CVar {F : Free} (env : ExeEnv F) : Free :=
  WithEv F env.trm2valCtx.toHasEv

end ExeEnv

/-- Adds the compile-time typing context to an execution environment. -/
class BuildEnv (F : Free) extends ExeEnv F

namespace BuildEnv

def trm2typCtx {F : Free} (env : BuildEnv F) : Fixpoint F AST.Trm2Typ :=
  @FixpointCtor.mkFixpoint F env.ctor AST.Trm2Typ

abbrev CTyp {F : Free} (env : BuildEnv F) : Free :=
  WithEv F env.trm2typCtx.toHasEv

end BuildEnv

end

end Lp2lc.Next.STLC
