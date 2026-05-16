import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.DTLC.Def

namespace Lp2lc.Active

open Util

namespace DTLC

namespace Trm

/-- Erasing annotations always produces a type-erased term. -/
theorem eraseType_isErased (I : Index) : ∀ (self : Trm I), self.typeEraseAll.TypeErased
| .val (.primitive _) _ => rfl
| .val (.fn body _) _ =>
  ⟨rfl, rfl, fun arg => eraseType_isErased I (body arg)⟩
| .apply fn arg _ =>
  ⟨rfl, eraseType_isErased I fn, eraseType_isErased I arg⟩
| .ref _ _ => rfl

/-- Replacing the outer annotation makes that annotation visible to semantic checking. -/
private theorem typeUpdate_typeGet {I : Index} (self : Trm I) (t : Option (Typ I)) :
    (self.typeUpdate t).typeGet = t := by
  cases self <;> rfl

/-- Successful value compilation emits an erased value satisfying the requested annotation. -/
private theorem valCompile_value {I : Index} {value : Val I} {t : Option (Typ I)}
    {compiled : Trm I} :
    value.compile t = .some (v := compiled) ->
      ∃ emitted, compiled = .val (v := emitted) (t := none) ∧
        ∀ checked_type,
          t = some checked_type ->
            emitted.satisfies checked_type = true := by
  cases t with
  | none =>
    cases value with
    | primitive repr =>
      intro h_compile
      simp [Val.compile, Trm.typeEraseAll] at h_compile
      subst compiled
      exact ⟨.primitive repr, rfl, by intro checked_type h_type; cases h_type⟩
    | fn body tIn =>
      intro h_compile
      simp [Val.compile, Trm.typeEraseAll] at h_compile
      subst compiled
      exact ⟨.fn (body := fun arg => (body arg).typeEraseAll) (tIn := none), rfl, by
        intro checked_type h_type
        cases h_type⟩
  | some checked_type =>
    cases h_satisfies : value.satisfies checked_type with
    | false =>
      intro h_compile
      simp [Val.compile, h_satisfies] at h_compile
    | true =>
      cases value with
      | primitive repr =>
        intro h_compile
        simp [Val.compile, h_satisfies, Trm.typeEraseAll] at h_compile
        subst compiled
        exact ⟨.primitive repr, rfl, by
          intro other_type h_type
          cases h_type
          exact h_satisfies⟩
      | fn body tIn =>
        intro h_compile
        simp [Val.compile, h_satisfies, Trm.typeEraseAll] at h_compile
        subst compiled
        exact ⟨.fn (body := fun arg => (body arg).typeEraseAll) (tIn := none), rfl, by
          intro other_type h_type
          cases h_type
          cases checked_type with
          | primitive =>
            simp [Val.satisfies] at h_satisfies
          | depFn tIn tOut =>
            rfl
          | top =>
            rfl⟩

/-- Successful compilation emits a value satisfying the source term annotation. -/
private theorem compile_value {I : Index} [FBound I Trm] {source compiled : Trm I}
    {fuel : Nat} :
    source.compile fuel = .some (v := compiled) ->
      ∃ value, compiled = .val (v := value) (t := none) ∧
        ∀ checked_type,
          source.typeGet = some checked_type ->
            value.satisfies checked_type = true := by
  induction fuel generalizing source compiled with
  | zero =>
    intro h_compile
    simp [Trm.compile] at h_compile
  | succ fuel ih =>
    cases source with
    | val value type_annotation =>
      intro h_compile
      exact valCompile_value (by simpa [Trm.compile] using h_compile)
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
                ih (source := (body (FBound.fwd compiled_arg)).typeUpdate type_annotation)
                  h_compile
              exact ⟨value, h_value, by
                intro checked_type h_type
                exact h_checked checked_type (by
                  simpa [Trm.typeUpdate_typeGet] using h_type)⟩
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
        ih (source := (FBound.rev (K := Trm) ref_value).typeUpdate type_annotation)
          (by simpa [Trm.compile] using h_compile)
      exact ⟨value, h_value, by
        intro checked_type h_type
        exact h_checked checked_type (by
          simpa [Trm.typeUpdate_typeGet] using h_type)⟩

/-- Successful compilation is adequate for the fuel used by the compiler. -/
theorem adequacy {I : Index} [FBound I Trm] [FBound I Val]
    {source compiled : Trm I} {fuel : Nat} :
    source.compile fuel = .some (v := compiled) ->
      source.Adequate compiled fuel := by
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
      ((body (FBound.fwd compiled_arg)).typeUpdate type_annotation).compile fuel =
        .some (v := compiled)) :
    (Trm.apply (fn := fn) (arg := arg) (t := type_annotation)).compile (fuel + 1) =
      Outcome.some (v := compiled) := by
  simp [Trm.compile, fn_compile, arg_compile, body_compile]

/-- Soundness of semantic typing through adequacy of successful compilation. -/
theorem soundness {I : Index} [FBound I Trm] [FBound I Val] {fuel : Nat}
    {source : Trm I} :
    source.Typing fuel ->
      ∃ compiled,
        source.compile fuel = .some (v := compiled) ∧
          source.Adequate compiled fuel := by
  unfold Trm.Typing
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

end DTLC

end Lp2lc.Active
