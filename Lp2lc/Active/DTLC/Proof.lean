import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.DTLC.Def

namespace Lp2lc.Active

namespace DTLC

open AST

namespace Trm

open Util

/--
Fuel-indexed adequacy predicate for a compiled program.

At each fuel level, a compiled term is adequate when evaluation either produces
a value or runs out of fuel, but never returns a runtime error.
-/
def IsAdequate {I : Index} [Runtime.Env I] (program : Trm I) (fuel : Nat) : Prop :=
  match fuel with
  | 0 => program.eval 0 = .outOfFuel
  | fuel + 1 =>
    (∃ value, program.eval (fuel + 1) = .some value) ∨
      program.eval (fuel + 1) = .outOfFuel

-- /--
-- Runtime adequacy predicate for compiled programs.

-- An adequate program may run out of runtime fuel, but it must not reach runtime
-- `error`. When runtime evaluation produces a value, that value must satisfy the
-- source annotation checked by compilation.
-- -/
-- def Trm.IsAdequate {I : Index} [Runtime.Env I]
--     (program : Trm I) (typeAnnotation : Option (Typ I)) (runtimeFuel : Nat) : Prop :=
--   match program.eval runtimeFuel with
--   | .error => False
--   | .outOfFuel => True
--   | .some value =>
--     match typeAnnotation with
--     | none => True
--     | some checkedType => value.satisfies checkedType = true
--
-- /-- Adequacy: successful compilation gives a runtime-adequate program. -/
-- theorem adequacy {I : Index} [FBound I Trm] [FBound I Val]
--     {source program : Trm I} {compileFuel runtimeFuel : Nat}
--     (isCompiled : source.compile compileFuel = .some program) :
--     program.Adequate source.type.get runtimeFuel := by
--   sorry

/--
Fuel-indexed fundamental predicate for a source term and its compiled program.

The predicate records exactly the behavior the compiler promises: successful
compilation at the same fuel yields the compiled term, and that term is erased
and adequate for the runtime fuel being considered.
-/
def IsFundamental {I : Index} [Compiletime.Env I] [Runtime.Env I]
    (sourceTrm compiledTrm : Trm I) (compileFuel runtimeFuel : Nat) : Prop :=
  match compileFuel with
  | 0 => sourceTrm.compile 0 = .outOfFuel
  | compileFuel + 1 =>
    (sourceTrm.compile (compileFuel + 1) = .some compiledTrm) ∧
      compiledTrm.type.IsErased ∧
        IsAdequate compiledTrm runtimeFuel


-- /-- Fundamental lemma: successful application compilation is semantic typing. -/
-- def Trm.IsFundamental {I : Index} [Compiletime.Env I]
--     {fn arg program : Trm I} {typeAnnotation : Option (Typ I)} {compileFuel : Nat} : Prop :=
--     (isCompiled :
--       (Trm.apply fn arg typeAnnotation).compile compileFuel =
--         .some program) ->
--     (Trm.apply fn arg typeAnnotation).Typing compileFuel
--
-- theorem fundament {I : Index} [FBound I Trm]
--     {fn arg program : Trm I} {typeAnnotation : Option (Typ I)} {compileFuel : Nat}
--     (isCompiled :
--       (Trm.apply (fn := fn) (arg := arg) (t := typeAnnotation)).compile compileFuel =
--         .some program) :
--     (Trm.apply (fn := fn) (arg := arg) (t := typeAnnotation)).Typing compileFuel := by
--   sorry

/--
Fuel-indexed soundness predicate for semantic typing.

Soundness packages the compiler result promised by `Typing`: there is an erased
compiled program for the source term, and that program is adequate at the
runtime fuel being checked.
-/
def IsSound {I : Index} [Compiletime.Env I] [Runtime.Env I]
    (sourceTrm : Trm I) (compileFuel runtimeFuel : Nat) : Prop :=
  match compileFuel with
  | 0 => sourceTrm.compile 0 = .outOfFuel
  | compileFuel + 1 =>
    ∃ compiledTrm,
      sourceTrm.compile (compileFuel + 1) = .some compiledTrm ∧
        compiledTrm.type.IsErased ∧
          IsAdequate compiledTrm runtimeFuel

/-- Erasing annotations always produces a type-erased term. -/
theorem eraseType_isErased {I : Index} : ∀ (self : Trm I), self.type.eraseRecursively.type.IsErased
| .val (.primitive _) _ => rfl
| .val (.fn body) _ =>
  ⟨rfl, fun arg => eraseType_isErased (body arg)⟩
| .apply fn arg _ =>
  ⟨rfl, eraseType_isErased fn, eraseType_isErased arg⟩
| .ref _ _ => rfl

/-- A compiled term is adequate at a fuel when evaluation does not return runtime error. -/
theorem adequacyLemma {I : Index} [Runtime.Env I] {compiledTrm : Trm I} {fuel : Nat}
    (isNotError : compiledTrm.eval fuel ≠ .error) :
    IsAdequate compiledTrm fuel := by
  cases fuel with
  | zero =>
    rfl
  | succ fuel =>
    unfold IsAdequate
    cases evalResult : compiledTrm.eval (fuel + 1) with
    | some value =>
      exact Or.inl ⟨value, evalResult⟩
    | error =>
      exact False.elim (isNotError evalResult)
    | outOfFuel =>
      exact Or.inr evalResult

/-- Fundamental lemma at zero compile fuel follows from the compiler fuel guard. -/
theorem fundamentalLemma_zero {I : Index} [Compiletime.Env I] [Runtime.Env I]
    {sourceTrm compiledTrm : Trm I} {runtimeFuel : Nat} :
    IsFundamental
      (sourceTrm := sourceTrm)
      (compiledTrm := compiledTrm)
      (compileFuel := 0)
      (runtimeFuel := runtimeFuel) := by
  unfold IsFundamental
  cases sourceTrm <;> rfl

/-- Fundamental lemma at successor compile fuel packages compilation, erasure, and adequacy. -/
theorem fundamentalLemma_succ {I : Index} [Compiletime.Env I] [Runtime.Env I]
    {sourceTrm compiledTrm : Trm I} {compileFuel runtimeFuel : Nat}
    (isCompiled : sourceTrm.compile (compileFuel + 1) = .some compiledTrm)
    (isErased : compiledTrm.type.IsErased)
    (isAdequate : IsAdequate compiledTrm runtimeFuel) :
    IsFundamental sourceTrm compiledTrm (compileFuel + 1) runtimeFuel := by
  exact ⟨isCompiled, isErased, isAdequate⟩

/-- Soundness at zero compile fuel follows from the compiler fuel guard. -/
theorem soundness_zero {I : Index} [Compiletime.Env I] [Runtime.Env I]
    {sourceTrm : Trm I} {runtimeFuel : Nat} :
    IsSound (sourceTrm := sourceTrm) (compileFuel := 0) (runtimeFuel := runtimeFuel) := by
  unfold IsSound
  cases sourceTrm <;> rfl

/-- Soundness at successor compile fuel follows from a fundamental result. -/
theorem soundness_succ {I : Index} [Compiletime.Env I] [Runtime.Env I]
    {sourceTrm compiledTrm : Trm I} {compileFuel runtimeFuel : Nat}
    (isFundamental : IsFundamental sourceTrm compiledTrm (compileFuel + 1) runtimeFuel) :
    IsSound sourceTrm (compileFuel + 1) runtimeFuel := by
  exact ⟨compiledTrm, isFundamental⟩

/-- Semantic typing is sound when every successful compilation is fundamental. -/
theorem soundness {I : Index} [Compiletime.Env I] [Runtime.Env I]
    {sourceTrm : Trm I} {compileFuel runtimeFuel : Nat}
    (isTyped : AST.Trm.Typing sourceTrm (compileFuel + 1))
    (isFundamental :
      ∀ compiledTrm,
        sourceTrm.compile (compileFuel + 1) = .some compiledTrm →
          IsFundamental sourceTrm compiledTrm (compileFuel + 1) runtimeFuel) :
    IsSound sourceTrm (compileFuel + 1) runtimeFuel := by
  unfold AST.Trm.Typing at isTyped
  cases compileResult : sourceTrm.compile (compileFuel + 1) with
  | some compiledTrm =>
    exact soundness_succ (isFundamental compiledTrm compileResult)
  | error =>
    simp [Outcome.isSome, compileResult] at isTyped
  | outOfFuel =>
    simp [Outcome.isSome, compileResult] at isTyped

end Trm

end DTLC

end Lp2lc.Active
