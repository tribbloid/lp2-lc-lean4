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

class FBound (I : Index) (K : Index -> Type) where -- fixed-point cast, looks like a reversed Env, it cast `Trm I` into something Val.depFn can accept
  fwd : K I -> I -- useful in eval, definition uses the inverse but interpreter is not allowed to see it.
  rev : I -> K I
  fwdRoundtrip : (value : K I) -> rev (fwd value) = value

attribute [simp] FBound.fwdRoundtrip

inductive Outcome (T : Index)
| some (v: T)
| error
| outOfFuel

namespace Outcome

def isSome : (self: Outcome T) -> Prop
| .some _ => true
| _ => false

end Outcome

section Syntax

variable (I : Index) -- index


mutual

/--
Type AST
-/
inductive Typ : Index where
| primitive
| depFn (tIn : Typ) (tOut : (arg : I) -> Typ)
| top -- type of anything, can bind both primitive and depFn.

-- def TAnno := Option Typ -- doesn't work in mutual block

/--
Term AST

Each AST can have optional type annotations, but they are only extra
constraint used in type-checking.

In HOAS there is no Context/Env to bind type to terms, so an optional type
annotation is the only realistic alternative. It shouldn't be confused with
intrinsic typing, which is impossible for Typ in the same mutual block.

In runtime, type annotations are ideally erased.
-/
inductive Trm : Index where
| val (v : Val) (t : Option Typ := by exact none)
| apply (fn : Trm) (arg : Trm) (t : Option Typ := by exact none)
| ref (s: I) (t : Option Typ := by exact none) -- binded reference, AKA variable/var

/--
Value AST, contains no ref and apply.

Only eval target and only accepted input of ANF (atomic normal form)

In runtime, type annotations are ideally erased.
-/
inductive Val : Index where
| primitive (repr : ByteCode) -- most specific type is always `primitive`
| fn (body : (arg : I) -> Trm)  (tIn : Option Typ := by exact none)-- most specific type is always `.depFn`

end

namespace Trm

def IsTypeErased {I : Index} (self: Trm I): Prop :=
  match self with
  | .val (.primitive _) t => t = none
  | .val (.fn body tIn) t => t = none ∧ tIn = none ∧ ∀ arg, IsTypeErased (body arg)
  | .apply fn arg t => t = none ∧ IsTypeErased fn ∧ IsTypeErased arg
  | .ref _ t => t = none

/-- Removes all optional type annotations from a term. -/
def eraseType {I : Index} (self: Trm I): Trm I :=
  match self with
  | .val (.primitive repr) _ => .val (.primitive repr) none
  | .val (.fn body _) _ => .val (.fn (body := fun arg => (body arg).eraseType) (tIn := none)) none
  | .apply fn arg _ => .apply fn.eraseType arg.eraseType none
  | .ref s _ => .ref s none

/-- Erasing annotations always produces a type-erased term. -/
theorem eraseType_isErased (I : Index) : ∀ (self : Trm I), self.eraseType.IsTypeErased
| .val (.primitive _) _ => rfl
| .val (.fn body _) _ => ⟨rfl, rfl, fun arg => eraseType_isErased I (body arg)⟩
| .apply fn arg _ => ⟨rfl, eraseType_isErased I fn, eraseType_isErased I arg⟩
| .ref _ _ => rfl

/-- Checks whether one annotation is compatible with another at its semantic head form. -/
private def typeCompatible {I : Index} (actual : Typ I) (expected : Typ I) : Bool :=
  match actual, expected with
  | .top, _ => true
  | _, .top => true
  | .primitive, .primitive => true
  | .depFn (tIn := _) (tOut := _), .depFn (tIn := _) (tOut := _) => true
  | _, _ => false

/-- Decidable semantic membership of a value in a type annotation. -/
private def valueSatisfiesType {I : Index} (value : Val I) (type_annotation : Typ I) : Bool :=
  match type_annotation with
  | .top => true
  | .primitive =>
    match value with
    | .primitive (repr := _) => true
    | .fn (body := _) (tIn := _) => false
  | .depFn (tIn := tIn) (tOut := _) =>
    match value with
    | .primitive (repr := _) => false
    | .fn (body := _) (tIn := none) => true
    | .fn (body := _) (tIn := some actual) => typeCompatible actual tIn

/-- Semantic typing predicate for values. -/
def valueSatisfies {I : Index} (value : Val I) (type_annotation : Typ I) : Prop :=
  valueSatisfiesType value type_annotation = true

/-- Reads the optional annotation attached to the outer term constructor. -/
def typeAnnotation {I : Index} (self : Trm I) : Option (Typ I) :=
  match self with
  | .val (v := _) (t := type_annotation) => type_annotation
  | .apply (fn := _) (arg := _) (t := type_annotation) => type_annotation
  | Trm.ref _ type_annotation => type_annotation

/-- Replaces only the outer annotation while preserving the underlying term. -/
def withType {I : Index} (self : Trm I) (type_annotation : Option (Typ I)) : Trm I :=
  match self with
  | .val (v := value) (t := _) => .val (v := value) (t := type_annotation)
  | .apply (fn := fn) (arg := arg) (t := _) => .apply (fn := fn) (arg := arg) (t := type_annotation)
  | Trm.ref ref_value _ => Trm.ref ref_value type_annotation

/-- Replacing the outer annotation makes that annotation visible to semantic checking. -/
private theorem withType_typeAnnotation {I : Index} (self : Trm I) (type_annotation : Option (Typ I)) :
    (self.withType type_annotation).typeAnnotation = type_annotation := by
  cases self <;> rfl

/-- Checks a value annotation and emits erased value syntax when it succeeds. -/
private def compileValue {I : Index} (value : Val I) (type_annotation : Option (Typ I)) : Outcome (Trm I) :=
  match type_annotation with
  | none => .some (v := (Trm.val (v := value) (t := none)).eraseType)
  | some type_annotation =>
    match valueSatisfiesType value type_annotation with
    | true => .some (v := (Trm.val (v := value) (t := none)).eraseType)
    | false => .error

/-- Successful value compilation emits an erased value satisfying the requested annotation. -/
private theorem compileValue_value {I : Index} {value : Val I} {type_annotation : Option (Typ I)}
    {compiled : Trm I} :
    compileValue value type_annotation = .some (v := compiled) ->
      ∃ emitted, compiled = .val (v := emitted) (t := none) ∧
        ∀ checked_type,
          type_annotation = some checked_type ->
            valueSatisfies emitted checked_type := by
  cases type_annotation with
  | none =>
    cases value with
    | primitive repr =>
      intro h_compile
      simp [compileValue, eraseType] at h_compile
      subst compiled
      exact ⟨.primitive repr, rfl, by intro checked_type h_type; cases h_type⟩
    | fn body tIn =>
      intro h_compile
      simp [compileValue, eraseType] at h_compile
      subst compiled
      exact ⟨.fn (body := fun arg => (body arg).eraseType) (tIn := none), rfl, by
        intro checked_type h_type
        cases h_type⟩
  | some checked_type =>
    cases h_satisfies : valueSatisfiesType value checked_type with
    | false =>
      intro h_compile
      simp [compileValue, h_satisfies] at h_compile
    | true =>
      cases value with
      | primitive repr =>
        intro h_compile
        simp [compileValue, h_satisfies, eraseType] at h_compile
        subst compiled
        exact ⟨.primitive repr, rfl, by
          intro other_type h_type
          cases h_type
          exact h_satisfies⟩
      | fn body tIn =>
        intro h_compile
        simp [compileValue, h_satisfies, eraseType] at h_compile
        subst compiled
        exact ⟨.fn (body := fun arg => (body arg).eraseType) (tIn := none), rfl, by
          intro other_type h_type
          cases h_type
          cases checked_type with
          | primitive =>
            simp [valueSatisfiesType] at h_satisfies
          | depFn tIn tOut =>
            rfl
          | top =>
            rfl⟩

/-- Normalizes source terms to values while spending fuel at each semantic descent -/
def eval {I : Index} [FBound I Val] (trm : Trm I) (fuel : Nat) : Outcome (Val I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val value _ => .some value
    | apply fn arg _ =>
      let anf := (fn.eval fuel, arg.eval fuel) -- ANF, atomic normal form
      match anf with
      | (.some (.fn body), .some value) => (body (FBound.fwd value)).eval fuel
      | (.outOfFuel, _) | (_, .outOfFuel)  => .outOfFuel
      | _ => .error
    | .ref s _ =>
      .some (FBound.rev s)

/--
fuel-guarded compiler API that verify a term (with optional type annotation),
and generate a more specialised, executable, type-erased term. This execution should always succeed (adequency lemma).

- compiling malformed term will fail
- compiling term with wrong annotation will fail
- always return outOfFuel if fuel drops to 0
- no term/application should be evaluated during compilation. The `FBound I Trm` condition (representing compiletime bindings) is deliberately different
  from `FBound I Val` (representing runtime binding) to avoid evaluation in compiletime.

semantic typing (a predicate on ) is merely this API being successful

this is a critical semantic rule for proving:

- adequecy lemma: a successfully compiled term can always be successfully executed (to
  a value that can be type-checked by the same type) or run out of fuel.
- fundamental lemma: if a type-annotated function and it's compatible argumennt
  can both be successfully compiled, then their applied form can also be
  successfull ccompiled.
- finally, soundness theorem that uses the above 2 lemma.
-/
def compile {I : Index} [FBound I Trm] (trm: Trm I) (fuel: Nat): Outcome (Trm I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val (v := value) (t := type_annotation) =>
      compileValue value type_annotation
    | .apply (fn := fn) (arg := arg) (t := type_annotation) =>
      let anf := (fn.compile fuel, arg.compile fuel)
      match anf with
      | (.some (.val (.fn body _) _), .some compiled_arg) =>
        ((body (FBound.fwd compiled_arg)).withType type_annotation).compile fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .error
    | Trm.ref ref_value type_annotation =>
      (Trm.withType (FBound.rev (K := Trm) ref_value) type_annotation).compile fuel

def typing {I : Index} [FBound I Trm](fuel: Nat)  (trm: Trm I) : Prop :=
  (trm.compile fuel).isSome

/-- Adequacy predicate relating successful compilation to fuel-guarded execution. -/
def adequate {I : Index} [FBound I Val] (source : Trm I) (compiled : Trm I)
    (fuel : Nat) : Prop :=
  compiled.eval fuel ≠ .error ∧
    ∀ checked_type value,
      source.typeAnnotation = some checked_type ->
        compiled.eval fuel = .some (v := value) ->
          valueSatisfies value checked_type

/-- Successful compilation emits a value satisfying the source term annotation. -/
private theorem compile_value {I : Index} [FBound I Trm] {source compiled : Trm I}
    {fuel : Nat} :
    source.compile fuel = .some (v := compiled) ->
      ∃ value, compiled = .val (v := value) (t := none) ∧
        ∀ checked_type,
          source.typeAnnotation = some checked_type ->
            valueSatisfies value checked_type := by
  induction fuel generalizing source compiled with
  | zero =>
    intro h_compile
    simp [Trm.compile] at h_compile
  | succ fuel ih =>
    cases source with
    | val value type_annotation =>
      intro h_compile
      exact compileValue_value (by simpa [Trm.compile] using h_compile)
    | apply fn arg type_annotation =>
      intro h_compile
      cases h_fn : fn.compile fuel with
      | some compiled_fn =>
        cases h_arg : arg.compile fuel with
        | some compiled_arg =>
          cases compiled_fn with
          | val fn_value fn_type =>
            cases fn_value with
            | primitive repr =>
              simp [Trm.compile, h_fn, h_arg] at h_compile
            | fn body fn_tIn =>
              simp [Trm.compile, h_fn, h_arg] at h_compile
              obtain ⟨value, h_value, h_checked⟩ :=
                ih (source := (body (FBound.fwd compiled_arg)).withType type_annotation) h_compile
              exact ⟨value, h_value, by
                intro checked_type h_type
                exact h_checked checked_type (by
                  simpa [Trm.withType_typeAnnotation] using h_type)⟩
          | apply fn' arg' fn_type =>
            simp [Trm.compile, h_fn, h_arg] at h_compile
          | ref ref fn_type =>
            simp [Trm.compile, h_fn, h_arg] at h_compile
        | error =>
          simp [Trm.compile, h_fn, h_arg] at h_compile
        | outOfFuel =>
          simp [Trm.compile, h_fn, h_arg] at h_compile
      | error =>
        cases h_arg : arg.compile fuel <;>
          simp [Trm.compile, h_fn, h_arg] at h_compile
      | outOfFuel =>
        simp [Trm.compile, h_fn] at h_compile
    | ref ref_value type_annotation =>
      intro h_compile
      obtain ⟨value, h_value, h_checked⟩ :=
        ih (source := Trm.withType (FBound.rev (K := Trm) ref_value) type_annotation)
          (by simpa [Trm.compile] using h_compile)
      exact ⟨value, h_value, by
        intro checked_type h_type
        exact h_checked checked_type (by
          simpa [Trm.withType_typeAnnotation] using h_type)⟩

/-- Successful compilation is adequate for the fuel used by the compiler. -/
theorem adequacy {I : Index} [FBound I Trm] [FBound I Val]
    {source compiled : Trm I} {fuel : Nat} :
    source.compile fuel = .some (v := compiled) ->
      source.adequate compiled fuel := by
  intro h_compile
  obtain ⟨value, h_value, h_checked⟩ := Trm.compile_value h_compile
  subst compiled
  cases fuel with
  | zero =>
    simp [Trm.compile] at h_compile
  | succ fuel =>
    constructor
    · simp [Trm.eval]
    · intro checked_type result h_type h_eval
      simp [Trm.eval] at h_eval
      cases h_eval
      exact h_checked checked_type h_type

/-- Fundamental compilation rule for a type-annotated dependent application. -/
theorem fundamental {I : Index} [FBound I Trm] {fn arg compiled_arg compiled : Trm I}
    {body : (arg : I) -> Trm I} {type_annotation : Option (Typ I)} {fuel : Nat}
    (fn_compile : fn.compile fuel =
      .some (v := .val (v := .fn (body := body) (tIn := none)) (t := none)))
    (arg_compile : arg.compile fuel = .some (v := compiled_arg))
    (body_compile :
      ((body (FBound.fwd compiled_arg)).withType type_annotation).compile fuel =
        .some (v := compiled)) :
    (Trm.apply (fn := fn) (arg := arg) (t := type_annotation)).compile (fuel + 1) =
      Outcome.some (v := compiled) := by
  simp [Trm.compile, fn_compile, arg_compile, body_compile]

/-- Soundness of semantic typing through adequacy of successful compilation. -/
theorem soundness {I : Index} [FBound I Trm] [FBound I Val] {fuel : Nat}
    {source : Trm I} :
    source.typing fuel ->
      ∃ compiled,
        source.compile fuel = .some (v := compiled) ∧
          source.adequate compiled fuel := by
  unfold Trm.typing
  cases h_compile : source.compile fuel with
  | some compiled =>
    intro _
    exact ⟨compiled, rfl, Trm.adequacy (source := source) (compiled := compiled) h_compile⟩
  | error =>
    intro h_typing
    simp [Outcome.isSome] at h_typing
  | outOfFuel =>
    intro h_typing
    simp [Outcome.isSome] at h_typing

end Trm

instance valIsTrm : Coe (Val I) (Trm I) where
  coe := (fun v => Trm.val v)

end Syntax

abbrev TypAST := {I : Index} -> Typ I

abbrev ValAST := {I : Index} -> Val I

abbrev TrmAST := {I : Index} -> Trm I

end DTLC

end Lp2lc.Active
