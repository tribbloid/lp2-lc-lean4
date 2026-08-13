import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace STLC

/- Shared STLC syntax family, currently exposing function types over the common representation. -/
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
| ref (s: F.Carrier) : AST F .Trm -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala), Evidence is required to proof that `x` is a valid index in the variable context
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
  trm : AST.Trm F
  val : AST.Val F

end

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

/--
Contains compiletime fixpoint bridges for semantic obligations of terms.

registered Trm2Typ must be relatable
-/
class BuildEnv extends F.FixpointCtor.{1}
  -- trmRefs :  -- TODO: this may be required for transparent inline function

namespace BuildEnv

def trm2typCtx (env : @BuildEnv F) : F.Fixpoint (AST.Trm2Typ F) :=
  env.mkFixpoint (AST.Trm2Typ F)

end BuildEnv

/--
Contains runtime fixpoint bridges for value assignment to terms.

registered Trm2Val must be relatable
-/

class ExeEnv extends F.FixpointCtor.{1}

namespace ExeEnv

def trm2valCtx (env : @ExeEnv F) : F.Fixpoint (AST.Trm2Val F) :=
  env.mkFixpoint (AST.Trm2Val F)

end ExeEnv

namespace AST
section variable [env: @ExeEnv F]

/--
Evaluates a term by spending 1 fuel at each semantic
descent. Runtime evaluation uses [Free.Fixpoint] for references and deliberately
does not inspect compile-time typing evidence.
-/
def eval (self : AST.Trm F) : RecOpt (AST.Val F)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      let anf := (fnTerm.eval fuel, arg.eval fuel) -- ANF, atomic normal form
      match anf with
      | (.yield (some (.lam body _tIn)), .yield (some input)) =>
        -- let permission := env.canSaveAny input
        let index := env.trm2valCtx.inv ⟨arg, input⟩
        (body index).eval fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | @AST.ref _ i =>
      .yield (some (env.trm2valCtx.get i).val)

end

end AST


end

end STLC

end Lp2lc.Active
