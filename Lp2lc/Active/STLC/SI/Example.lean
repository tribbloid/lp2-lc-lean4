import «Lp2lc».Active.STLC.SI.Def

namespace Lp2lc.Active.STLC

namespace SI

namespace Example

open scoped TypeNotation

def x : Var := ⟨"x"⟩
def y : Var := ⟨"y"⟩

def x_var : Term Ty.base := Term.term_variable (type := Ty.base) x

def id_term : Term (Ty.base :=> Ty.base) :=
  Term.lambda (input := Ty.base) (output := Ty.base) x x_var

def id_app_term : Term Ty.base :=
  Term.apply (input := Ty.base) (output := Ty.base) id_term Term.unit

def x_env : Env := [(x, Ty.base)]
def shadow_env : Env := [(x, Ty.base :=> Ty.base), (x, Ty.base)]

def unit_scoped : ScopedTerm [] Ty.base := ⟨Term.unit, by simp [IsScoped]⟩

def id_scoped : ScopedTerm [] (Ty.base :=> Ty.base) := ⟨id_term, by
  simp [id_term, x_var, IsScoped, Env.get]
⟩

def id_app_scoped : ScopedTerm [] Ty.base := ⟨id_app_term, by
  simp [id_app_term, id_term, x_var, IsScoped, Env.get]
⟩

def base_value : Denotation Ty.base := PUnit.unit
def id_value : Denotation (Ty.base :=> Ty.base) := fun value => value

abbrev empty_evaluator : Evaluator := Evaluator.empty

def x_evaluator : Evaluator :=
  empty_evaluator.extend (input := Ty.base) x PUnit.unit

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
    simp [x_env, x_var, IsScoped, Env.get]
  true

#guard
  let _ : IsScoped [] Term.unit := by
    simp [IsScoped]
  true

#guard
  let _ : IsScoped [] id_term := by
    simp [id_term, x_var, IsScoped, Env.get]
  true

#guard
  let _ : IsScoped [] id_app_term := by
    simp [id_app_term, id_term, x_var, IsScoped, Env.get]
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
  let _ : base_value = PUnit.unit := rfl
  true

#guard
  let _ : id_value PUnit.unit = PUnit.unit := rfl
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
  let _ : x_evaluator.lookup x Ty.base rfl = PUnit.unit := by
    simp [x_evaluator, empty_evaluator, Evaluator.extend]
  true

#guard
  let _ : shadow_evaluator.lookup x (Ty.base :=> Ty.base) rfl PUnit.unit = PUnit.unit := by
    simp [shadow_evaluator, x_evaluator, id_value, Evaluator.extend]
  true

end Extend

namespace Denote

#guard
  let _ : empty_evaluator.denote unit_scoped = PUnit.unit := rfl
  true

#guard
  let _ : empty_evaluator.denote id_scoped PUnit.unit = PUnit.unit := rfl
  true

#guard
  let _ : empty_evaluator.denote id_app_scoped = PUnit.unit := rfl
  true

end Denote

end Example

end SI

end Lp2lc.Active.STLC
