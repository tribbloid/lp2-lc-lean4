import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC

namespace Example

def x : Var := ⟨"x"⟩
def y : Var := ⟨"y"⟩

def x_var : Term Ty.base := Term.term_variable (type := Ty.base) x

def id_term : Term (Ty.base :=> Ty.base) :=
  Term.lambda (input := Ty.base) (output := Ty.base) x x_var

def id_app_term : Term Ty.base :=
  Term.apply (input := Ty.base) (output := Ty.base) id_term Term.unit

def x_env : Env := [(x, Ty.base)]
def shadow_env : Env := [(x, Ty.base :=> Ty.base), (x, Ty.base)]

def unit_scoped : ScopedTerm [] Ty.base := ⟨Term.unit, by simp⟩

def id_scoped : ScopedTerm [] (Ty.base :=> Ty.base) := ⟨id_term, by
  simp [id_term, x_var]
⟩

def id_app_scoped : ScopedTerm [] Ty.base := ⟨id_app_term, by
  simp [id_app_term, id_term, x_var]
⟩

def base_value : Ty.base.Denotation := Unit.unit
def id_value : (Ty.base :=> Ty.base).Denotation := fun value => value

abbrev empty_evaluator : Evaluator := Evaluator.empty

def x_evaluator : Evaluator :=
  empty_evaluator.extend (input := Ty.base) x Unit.unit

def shadow_evaluator : Evaluator :=
  x_evaluator.extend (input := Ty.base :=> Ty.base) x id_value

namespace Later

#guard
  let later_step : Later (1 + 1 = 2) := ⟨by decide⟩
  let _ : 1 + 1 = 2 := later_step.force
  true

end Later

namespace Ty

#guard
  let _ : (Ty.base :=> Ty.base :=> Ty.base) = Ty.arrow Ty.base (Ty.arrow Ty.base Ty.base) := rfl
  true

end Ty

namespace Term

#guard
  let _ : x_var = Term.term_variable (type := Ty.base) x := rfl
  true

#guard
  let _ : id_term = Term.lambda (input := Ty.base) (output := Ty.base) x x_var := rfl
  true

#guard
  let _ : id_app_term = Term.apply (input := Ty.base) (output := Ty.base) id_term Term.unit := rfl
  true

end Term

namespace Env

#guard
  let _ : x_env = [(x, Ty.base)] := rfl
  true

#guard
  let _ : Env.get y x_env = none := rfl
  true

#guard
  let _ : Env.get x shadow_env = some (Ty.base :=> Ty.base) := rfl
  true

end Env

namespace IsScoped

#guard
  let _ : IsScoped x_env x_var := by
    simp [x_env, x_var]
  true

#guard
  let _ : IsScoped [] Term.unit := by
    simp
  true

#guard
  let _ : IsScoped [] id_term := by
    simp [id_term, x_var]
  true

#guard
  let _ : IsScoped [] id_app_term := by
    simp [id_app_term, id_term, x_var]
  true

end IsScoped

namespace ScopedTerm

#guard
  let _ : ScopedTerm [] Ty.base := unit_scoped
  true

#guard
  let _ : ScopedTerm [] (Ty.base :=> Ty.base) := id_scoped
  true

#guard
  let _ : ScopedTerm [] Ty.base := id_app_scoped
  true

end ScopedTerm

namespace Denotation

#guard
  let _ : base_value = Unit.unit := rfl
  true

#guard
  let _ : id_value Unit.unit = Unit.unit := rfl
  true

end Denotation

namespace Evaluator

#guard
  let _ : empty_evaluator.env = ([] : Env) := rfl
  true

#guard
  let _ : x_evaluator.env = x_env := rfl
  true

#guard
  let _ : shadow_evaluator.env = shadow_env := rfl
  true

end Evaluator

namespace Extend

#guard
  let _ : x_evaluator.lookup x Ty.base rfl = Unit.unit := by
    simp [x_evaluator, empty_evaluator]
  true

#guard
  let _ : shadow_evaluator.lookup x (Ty.base :=> Ty.base) rfl Unit.unit = Unit.unit := by
    simp [shadow_evaluator, x_evaluator, id_value]
  true

end Extend

namespace Denote

#guard
  let _ : empty_evaluator.denote unit_scoped = Unit.unit := rfl
  true

#guard
  let _ : empty_evaluator.denote id_scoped Unit.unit = Unit.unit := rfl
  true

#guard
  let _ : empty_evaluator.denote id_app_scoped = Unit.unit := rfl
  true

end Denote

namespace Semantics

#guard
  let _ : Semantics Ty.base 3 base_value := by
    simp [Semantics]
  true

#guard
  let _ : Semantics (Ty.base :=> Ty.base) 2 id_value := by
    intro _ _ _ _
    exact ⟨by simp [Semantics]⟩
  true

end Semantics

namespace EnvironmentSemantics

#guard
  let _ : EnvironmentSemantics empty_evaluator 4 := by
    intro name type binding
    simp at binding
  true

#guard
  let _ : EnvironmentSemantics x_evaluator 1 := by
    simpa [x_evaluator, base_value] using
      (extend_semantics
        (evaluator := empty_evaluator)
        (steps := 1)
        (name := x)
        (value := base_value)
        (by
          intro name type binding
          simp at binding)
        (by
          simp [Semantics]))
  true

end EnvironmentSemantics

namespace Fundamental

#guard
  let _ : Semantics (Ty.base :=> Ty.base) 2 (empty_evaluator.denote id_scoped) := by
    exact fundamental empty_evaluator id_scoped (steps := 2) (by
      intro name type binding
      simp at binding)
  true

#guard
  let _ : Semantics Ty.base 2 (empty_evaluator.denote id_app_scoped) := by
    exact fundamental empty_evaluator id_app_scoped (steps := 2) (by
      intro name type binding
      simp at binding)
  true

end Fundamental

namespace Soundness

#guard
  let _ : Semantics (Ty.base :=> Ty.base) 2 (Evaluator.empty.denote id_scoped) :=
    soundness id_scoped 2
  true

#guard
  let _ : Semantics Ty.base 2 (Evaluator.empty.denote id_app_scoped) :=
    soundness id_app_scoped 2
  true

end Soundness

end Example

end STLC
