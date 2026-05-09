import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

universe u v

-- 1. Implicitly lift a type to a higher universe using ULift
/-- Coerce a lower-universe type into a higher universe through `ULift`. -/
instance _autoUliftType : Coe (Type u) (Type (max u v)) where
  coe := ULift

-- 2. Implicitly lift the values of that type into the ULift wrapper, these 2 enabled universe cumulativity in rocq
/-- Coerce a value into the `ULift` carrier chosen by the lifted type. -/
instance _autoUliftValue {α : Type u} : Coe α (ULift.{v, u} α) where
  coe := ULift.up

structure K : Type

abbrev K1: Type 1 := K

open Util

/-- Universe-1 carrier for PHOAS indices. -/
abbrev Index := Type

section Syntax

variable (I : Index) -- index

mutual

inductive Typ : Index where
| primitive
| depFn (tIn : Typ) (tOut : (arg : I) -> Typ)
| top -- type of anything, can bind both primitive and depFn.

inductive Trm : Index where
| val (v : Val)
| depApply (fn : Trm) (arg : Trm)

inductive Val : Index where
| primitive (repr : ByteCode)
| fn (body : (arg : I) -> Trm)

end

instance valIsTrm : Coe (Val I) (Trm I) where
  coe := (fun v => Trm.val v)

end Syntax

class FBound (I : Index) where -- fixed-point cast, looks like a reversed Env, it cast `Trm I` into something Val.depFn can accept
  fwd: Val I -> I -- useful in eval, definition uses the inverse but interpreter is not allowed to see it.

inductive Outcome (T : Index)
| some (v: T)
| error
| outOfFuel

namespace Outcome

def isSome : (self: Outcome T) -> Prop
| .some _ => true
| _ => false

end Outcome

/-- Normalizes source terms to values while spending fuel at each semantic descent -/
def Trm.eval {I : Index} [FBound I] (trm : Trm I) (fuel : Nat) : Outcome (Val I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val value => .some value
    | .depApply fn arg =>
      match fn.eval fuel, arg.eval fuel with
      | .some (.fn body), .some value => (body (FBound.fwd value)).eval fuel
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .error

/-- Semantic membership of an evaluated value in a type annotation. -/
def Val.satisfies {I : Index} (value : Val I) (typeAnnotation : Typ I) : Prop :=
  match typeAnnotation with
  | .primitive => ∃ repr, value = .primitive repr
  | .depFn _ _ => ∃ body, value = .fn body
  | .top => ∃ topValue, value = topValue

/--
fuel-guarded compiler API that verify a type-annotated term and:

- if semantic type-check succeeds, generate a more specialised, executable term. This execution should always succeed (adequency lemma).
- else if type-check fails, return error
- always return outOfFuel if fuel drops to 0

semantic typing (a predicate on ) is merely this API being successful

this is a critical semantic rule for proving:

- adequecy lemma: a successfully compiled term can always be successfully executed (to
  a value that can be type-checked by the same type) or run out of fuel.
- fundamental lemma: if a type-annotated function and it's compatible argumennt
  can both be successfully compiled, then their applied form can also be
  successfull ccompiled.
- finally, soundness theorem that uses the above 2 lemma
-/
def Trm.compile {I : Index} [FBound I] (trm: Trm I) (fuel: Nat) (typeAnnotation: Typ I): Outcome (Trm I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .depApply fn arg =>
      match fn.eval fuel, arg.eval fuel with
      | .some (.fn body), .some value => (body (FBound.fwd value)).compile fuel typeAnnotation
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .error
    | .val value =>
      match typeAnnotation with
      | .primitive =>
        match value with
        | .primitive _ => .some (.val value)
        | .fn _ => .error
      | .depFn _ _ =>
        match value with
        | .primitive _ => .error
        | .fn _ => .some (.val value)
      | .top => .some (.val value)

/-- Runtime property required from a compiled term by semantic adequacy. -/
def Trm.adequate {I : Index} [FBound I] (compiled : Trm I) (fuel : Nat)
    (typeAnnotation : Typ I) : Prop :=
  compiled.eval fuel ≠ .error ∧
    ∀ (value : Val I), compiled.eval fuel = .some value -> value.satisfies typeAnnotation

def Trm.typing {I : Index} [FBound I] (typeAnnotation: Typ I) (fuel: Nat)  (trm: Trm I) : Prop :=
  (trm.compile fuel typeAnnotation).isSome

/-- Successful compilation produces a value term satisfying the requested annotation. -/
private theorem Trm.compile_value {I : Index} [FBound I] {trm compiled : Trm I}
    {fuel : Nat} {typeAnnotation : Typ I} :
    trm.compile fuel typeAnnotation = .some compiled ->
      ∃ value, compiled = .val value ∧ value.satisfies typeAnnotation := by
  induction fuel generalizing trm compiled typeAnnotation with
  | zero =>
    intro hCompile
    simp [Trm.compile] at hCompile
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases typeAnnotation with
      | primitive =>
        cases value with
        | primitive repr =>
          intro hCompile
          cases hCompile
          exact ⟨.primitive repr, rfl, ⟨repr, rfl⟩⟩
        | fn body =>
          intro hCompile
          simp [Trm.compile] at hCompile
      | depFn tIn tOut =>
        cases value with
        | primitive repr =>
          intro hCompile
          simp [Trm.compile] at hCompile
        | fn body =>
          intro hCompile
          cases hCompile
          exact ⟨.fn body, rfl, ⟨body, rfl⟩⟩
      | top =>
        intro hCompile
        cases hCompile
        exact ⟨value, rfl, ⟨value, rfl⟩⟩
    | depApply fn arg =>
      intro hCompile
      cases hFn : fn.eval fuel with
      | some fnValue =>
        cases hArg : arg.eval fuel with
        | some value =>
          cases fnValue with
          | primitive repr =>
            simp [Trm.compile, hFn, hArg] at hCompile
          | fn body =>
            simp [Trm.compile, hFn, hArg] at hCompile
            exact ih hCompile
        | error =>
          simp [Trm.compile, hFn, hArg] at hCompile
        | outOfFuel =>
          simp [Trm.compile, hFn, hArg] at hCompile
      | error =>
        cases hArg : arg.eval fuel <;>
          simp [Trm.compile, hFn, hArg] at hCompile
      | outOfFuel =>
        simp [Trm.compile, hFn] at hCompile

/-- Adequacy of semantic compilation for the fuel used by the compiler. -/
theorem Trm.adequacy {I : Index} [FBound I] {trm compiled : Trm I}
    {fuel : Nat} {typeAnnotation : Typ I} :
    trm.compile fuel typeAnnotation = .some compiled ->
      compiled.adequate fuel typeAnnotation := by
  intro hCompile
  obtain ⟨value, hCompiled, hValue⟩ := Trm.compile_value hCompile
  subst compiled
  cases fuel with
  | zero =>
    simp [Trm.compile] at hCompile
  | succ fuel =>
    constructor
    · simp [Trm.eval]
    · intro result hEval
      simp [Trm.eval] at hEval
      cases hEval
      exact hValue

/-- Fundamental compilation rule for a dependent application after runtime substitution. -/
theorem Trm.fundamental {I : Index} [FBound I] {fn arg : Trm I}
    {body : (arg : I) -> Trm I} {value : Val I} {typeAnnotation : Typ I}
    {fuel : Nat} {compiled : Trm I}
    (fnEval : fn.eval fuel = .some (.fn (body := body)))
    (argEval : arg.eval fuel = .some value)
    (bodyCompile : (body (FBound.fwd value)).compile fuel typeAnnotation = .some compiled) :
    (Trm.depApply fn arg).compile (fuel + 1) typeAnnotation = Outcome.some compiled := by
  simp [Trm.compile, fnEval, argEval, bodyCompile]

/-- Soundness of semantic typing through successful compilation. -/
theorem Trm.soundness {I : Index} [FBound I] {trm : Trm I} {fuel : Nat}
    {typeAnnotation : Typ I} :
    trm.typing typeAnnotation fuel ->
      ∃ compiled, trm.compile fuel typeAnnotation = .some compiled ∧
        compiled.adequate fuel typeAnnotation := by
  unfold Trm.typing
  cases hCompile : trm.compile fuel typeAnnotation with
  | some compiled =>
    intro _
    exact ⟨compiled, rfl,
      Trm.adequacy (trm := trm) (compiled := compiled) (fuel := fuel)
        (typeAnnotation := typeAnnotation) hCompile⟩
  | error =>
    intro hTyping
    simp [Outcome.isSome] at hTyping
  | outOfFuel =>
    intro hTyping
    simp [Outcome.isSome] at hTyping



end DTLC

end Lp2lc.Active
