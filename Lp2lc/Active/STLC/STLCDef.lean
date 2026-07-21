import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace STLC

/- Shared STLC syntax family, currently exposing function types over the common representation. -/
open Lp2lc.Active.Util

section variable {F : Free}

namespace AST
section variable (F : Free)

mutual

/--
Source type syntax.

`primitive` classifies primitive bytecode values and `fn` classifies functions.
-/
inductive Typ : Type where
| primitive -- `AnyVal` in Scala, accepts only primitive values
| fn (tIn : Typ) (tOut : Typ) -- function

/--
Source term syntax.

Primitive value terms are self-typed, while function values carry their input
type. Applications and references are unannotated.

In HOAS there is no syntax-level context binding terms to types, so function
input annotations are the extrinsic typing evidence available to the compiler.
They are not intrinsic typing indices on terms.
-/

inductive Trm : Type where
| val (v : Val) -- AKA literal
| apply (fn : Trm) (arg : Trm) -- fn must be a function that can be applied on arg
| ref (s: F.Index) -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala)


/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Function values carry their input type so the compiler can type-check HOAS bodies.
-/
inductive Val : Type where
| primitive (repr : F.Data) -- most specific type is always `primitive`
| fn (body : (arg : F.Index) → Trm) (tIn : Typ) -- most specific type is always `.fn tIn _`

end
end
end AST

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
    | isFalse notEqual, _ => isFalse (λ equality => notEqual (AST.Typ.fn.inj equality).1)
    | _, isFalse notEqual => isFalse (λ equality => notEqual (AST.Typ.fn.inj equality).2)

class RuntimeEnv where
  CanSave : Permission (AST.Val F)
  -- valueRefGen {TP: Type} : DepFBound (TP -> I.Index) (TP -> { value : AST.Val I // CanSave value }) -- TODO: don't know how to define this prior
  valueRefs: FBound F.Index { value : AST.Val F // CanSave value }
  canEvalAny: (v: AST.Val F) -> CanSave v

abbrev Condition (I : Free) := (value : AST.Val I) -> Prop -- AKA semantic type. TODO: this should be made irrelevant to I being chosen.

namespace AST.Trm
section variable [env: @RuntimeEnv F]

/--
Evaluates a term by spending 1 fuel at each semantic
descent. Runtime evaluation uses `FBound I Val` for references and deliberately
does not inspect compile-time typing evidence.
-/
def eval (self : AST.Trm F) : RecOption (AST.Val F)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fn arg =>
      let anf := (fn.eval fuel, arg.eval fuel) -- ANF, atomic normal form
      match anf with
      | (.yield (some (.fn body _tIn)), .yield (some input)) =>
        let permission := env.canEvalAny input
        let index := env.valueRefs.save ⟨input, permission⟩
        (body index).eval fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | @AST.Trm.ref _ i =>
      .yield (some (env.valueRefs.load i).1)

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
end AST.Trm

-- namespace Internal

-- /--
-- a compiled term with safety proof
-- -/
-- private structure _AdequateTrm (condition : Condition I) where
--   trm: AST.Trm I
--   safetyEv: trm.IsSafeBy condition

-- end Internal

-- abbrev AdequateTrm := @Internal._AdequateTrm I

-- namespace AdequateTrm
-- section variable {c: Condition I} (self: AdequateTrm c) [env : @RuntimeEnv I]

-- def eval : MaySucceed ({v : AST.Val I // c v}) := fun fuel =>
--   match h : self.trm.eval fuel with
--   | .result value =>
--     ⟨.result ⟨value, by
--       have evidence := self.safetyEv fuel
--       simpa [h] using evidence⟩, by
--         simp [Outcome.isResultOrOutOfFuel]⟩
--   | .error =>
--     have noError := self.safetyEv fuel
--     False.elim (by
--       simp [h] at noError)
--   | .outOfFuel =>
--     ⟨.outOfFuel, by
--       simp [Outcome.isResultOrOutOfFuel]⟩

-- end
-- end AdequateTrm

/--
Contains compile-time FBound bridges for semantic obligations.
-/
class CompilerEnv : Type where
  -- trmRefs :  -- TODO: this may be required for transparent inline function
  typeRefs : FBound F.Index (AST.Typ F)

section variable [env: @CompilerEnv F]
open AST

namespace AST.Trm
section variable (self : Trm F)

/--
AKA compile, recursively produce a proof target.

it is NOT guaranteed to terminate, but termination is the prior condition to be
used in Fundamental theorem (thus the `_total` suffix)

Structurally it should be similar to infer, but return `.some Unit` or `.none` instead of a precise type bound
-/
def recCanInhabit (self : Trm F) (typ : Typ F) : RecOption Unit :=
  sorry

/--
determine if a term can can inhabit a type bound.
-/
def CanInhabit_total (self : Trm F) (typ : Typ F) : Prop :=
  RecOption.isDecidable (self.recCanInhabit typ)

end
end AST.Trm

/-- Interprets source types as semantic conditions over values. -/
def AST.Typ.ToCondition (typ: Typ F): Condition F := λ value =>
  let trm := Trm.val value
  (trm.CanInhabit_total typ)

-- /-- States that syntactic typing entails semantic typing by the interpreted type. -/
-- def RecFundamental :=
--   ∀ (term : Trm I) (type : Typ I),
--     Rec (term.CanInhabit type → (term.SemiCanSatisfy (type.ToCondition)))


/-- States that syntactic typing entails semantic typing by the interpreted type. -/
def Fundamental : Prop :=
  ∀ (term : Trm F) (type : Typ F),
  ∀ (compilerFuel: Nat),
    term.recCanInhabit type compilerFuel = .yield (some ()) → term.CanSatisfy_semi (type.ToCondition)

-- /-- States that syntactic typing entails semantic typing by the interpreted type. -/
-- def Fundamental : Prop :=
--   ∀ (term : Trm I) (type : Typ I),
--     term.CanInhabit type → term.SemiCanSatisfy (type.ToCondition)

def fundamentalProof : @Fundamental F := by
  sorry

end


end
end STLC

end Lp2lc.Active
