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
| ref (s: F.Index) : AST F .Trm -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala), Evidence is required to proof that `x` is a valid index in the variable context
/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Function values carry their input type so the compiler can type-check HOAS bodies.
-/
| lit (repr : F.Data) : AST F .Val -- most specific type is always `primitive`
| lam (body : (arg : F.Index) → AST F .Trm) (tIn : AST F .Typ) : AST F .Val -- most specific type is always `.fn tIn _`


namespace AST

abbrev Typ (F : Free) := AST F .Typ
abbrev Trm (F : Free) := AST F .Trm
abbrev Val (F : Free) := AST F .Val

-- /-- Rebuilds syntax over the peer `Free` family whose evidence predicate is `True`. -/
-- def weaken : (self : AST F label) → AST F.weaken label
--   | .primitive => .primitive
--   | .fn tIn tOut => .fn tIn.weaken tOut.weaken
--   | .val value => .val value.weaken
--   | .apply fnTerm arg => .apply fnTerm.weaken arg.weaken
--   | .ref index => .ref index
--   | .lit repr => .lit repr
--   | .lam body tIn => .lam (λ arg => (body arg).weaken) tIn.weaken

-- instance weakenCoe {label : Label} :
--     Coe (AST F label) (AST F.weaken label) :=
--   ⟨weaken⟩

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
class CompilerEnv extends F.HasFixpoint
  -- trmRefs :  -- TODO: this may be required for transparent inline function

namespace CompilerEnv
def trm2typCtx (env : @CompilerEnv F) : F.Fixpoint (AST.Trm2Typ F) :=
  env.mkFixpoint (AST.Trm2Typ F)
end CompilerEnv

/--
Contains runtime fixpoint bridges for value assignment to terms.

registered Trm2Val must be relatable
-/
class RuntimeEnv extends F.HasFixpoint

namespace RuntimeEnv
def trm2valCtx (env : @RuntimeEnv F) : F.Fixpoint (AST.Trm2Val F) :=
  env.mkFixpoint (AST.Trm2Val F)
end RuntimeEnv

abbrev Condition (I : Free) := (value : AST.Val I) -> Prop -- AKA semantic type. TODO: this should be made irrelevant to I being chosen.

namespace AST
section variable [env: @RuntimeEnv F]

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
        let index := env.trm2valCtx.getUID ⟨arg, input⟩
        (body index).eval fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | @AST.ref _ i =>
      .yield (some (env.trm2valCtx.inv i).val)

end

section variable (self : AST.Trm F)

def recCanSatisfy (condition : Condition F) : ∀ [@RuntimeEnv F], Rec Prop := λ fuel =>
  (self.eval fuel).map (λ
    | some v => condition v
    | none => False)

/--
An safe term may run out of runtime fuel, but it must not reach runtime
`error`. When a runtime value is produced, it must satisfy the condition.
-/
def CanSatisfy_semi (condition : Condition F) : Prop :=
  ∀ fuel, ∀ [@RuntimeEnv F], (self.recCanSatisfy condition fuel).getOrElse True

/-- Converts semantic outcomes into obligations over all fuel and runtime environments. -/
abbrev WeakestPre := @CanSatisfy_semi F -- weakest precondition in Iris framework

def IsSafe : Prop :=
  self.CanSatisfy_semi (λ _ => true)

end

section variable [env: @CompilerEnv F]

section variable (self : Trm F)

/--
AKA compile, recursively produce a proof target.

it is NOT guaranteed to terminate, but termination is the prior condition to be
used in Fundamental theorem (thus the `_total` suffix)

Structurally it should be similar to infer, but return `.some Unit` or `.none` instead of a precise type bound
-/
def recCanInhabit (self : Trm F) (typ : Typ F) : RecOpt Unit :=
  sorry

/--
determine if a term can can inhabit a type bound.
-/
def CanInhabit_total (self : Trm F) (typ : Typ F) : Prop :=
  RecOption.isDecidable (self.recCanInhabit typ)

end
end
end AST

/-- Interprets source types as semantic conditions over values. -/
def AST.ToCondition (typ: Typ F): Condition F := λ value =>
  let trm := AST.val value
  (trm.CanInhabit_total typ)

-- /-- States that syntactic typing entails semantic typing by the interpreted type. -/
-- def RecFundamental :=
--   ∀ (term : Trm I) (type : Typ I),
--     Rec (term.CanInhabit type → (term.SemiCanSatisfy (type.ToCondition)))


-- TODO: this is actually not used ( preferring umbral compiler), need to decide which definition to use
/-- States that syntactic typing entails semantic typing by the interpreted type. -/
def Fundamental : Prop :=
  ∀ (term : Trm F) (type : Typ F),
  ∀ (compilerFuel: Nat),
    term.recCanInhabit type compilerFuel = .yield (some ()) → term.CanSatisfy_semi (type.ToCondition)

end

end STLC

end Lp2lc.Active
