import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC

namespace Example

def x : Var := ⟨"x"⟩
def y : Var := ⟨"y"⟩

def x_var : Term Ty.base := Term.term_variable (type := Ty.base) x

def id_term : Term (Ty.base :=> Ty.base) :=
  Term.lambda (tyIn := Ty.base) (tyOut := Ty.base) x x_var

def id_app_term : Term Ty.base :=
  Term.apply (tyIn := Ty.base) (tyOut := Ty.base) id_term (Term.literal "base_const")

def x_env : Env := [(x, Ty.base)]
def shadow_env : Env := [(x, Ty.base :=> Ty.base), (x, Ty.base)]

def const_scoped : Env.empty.ScopedTerm Ty.base := ⟨Term.literal "base_const", by simp⟩

def id_scoped : Env.empty.ScopedTerm (Ty.base :=> Ty.base) := ⟨id_term, by
  simp [id_term, x_var]
⟩

def id_app_scoped : Env.empty.ScopedTerm Ty.base := ⟨id_app_term, by
  simp [id_app_term, id_term, x_var]
⟩

def base_value : Ty.base.Denotation := "base_const"
def id_value : (Ty.base :=> Ty.base).Denotation := fun value => value

abbrev empty_repl : REPL := REPL.empty

def x_repl : REPL :=
  empty_repl.extend (input := Ty.base) x base_value

def shadow_repl : REPL :=
  x_repl.extend (input := Ty.base :=> Ty.base) x id_value

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
  let _ : id_term = Term.lambda (tyIn := Ty.base) (tyOut := Ty.base) x x_var := rfl
  true

#guard
  let _ : id_app_term =
      Term.apply (tyIn := Ty.base) (tyOut := Ty.base) id_term (Term.literal "base_const") := rfl
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
  let _ : x_env.IsScoped x_var := by
    simp [x_env, x_var]
  true

#guard
  let _ : Env.empty.IsScoped (Term.literal "base_const") := by
    simp
  true

#guard
  let _ : Env.empty.IsScoped id_term := by
    simp [id_term, x_var]
  true

#guard
  let _ : Env.empty.IsScoped id_app_term := by
    simp [id_app_term, id_term, x_var]
  true

end IsScoped

namespace ScopedTerm

#guard
  let _ : Env.empty.ScopedTerm Ty.base := const_scoped
  true

#guard
  let _ : Env.empty.ScopedTerm (Ty.base :=> Ty.base) := id_scoped
  true

#guard
  let _ : Env.empty.ScopedTerm Ty.base := id_app_scoped
  true

end ScopedTerm

namespace Denotation

#guard
  let _ : base_value = "base_const" := rfl
  true

#guard
  let _ : id_value "base_const" = "base_const" := rfl
  true

end Denotation

namespace REPL

#guard
  let _ : empty_repl.env = ([] : Env) := rfl
  true

#guard
  let _ : x_repl.env = x_env := rfl
  true

#guard
  let _ : shadow_repl.env = shadow_env := rfl
  true

end REPL

namespace Extend

#guard
  let _ : x_repl.varLookup x Ty.base rfl = "base_const" := by
    simp [x_repl, empty_repl, base_value]
  true

#guard
  let _ : shadow_repl.varLookup x (Ty.base :=> Ty.base) rfl "base_const" = "base_const" := by
    simp [shadow_repl, x_repl, id_value]
  true

end Extend

namespace Denote

#guard
  let _ : empty_repl.eval const_scoped = "base_const" := rfl
  true

#guard
  let _ : empty_repl.eval id_scoped "base_const" = "base_const" := rfl
  true

#guard
  let _ : empty_repl.eval id_app_scoped = "base_const" := by
    change ("base_const" : String) = "base_const"
    rfl
  true

end Denote

namespace Semantics

#guard
  let _ : Semantics Ty.base base_value 3 := by
    simp [Semantics]
  true

#guard
  let _ : Semantics (Ty.base :=> Ty.base) id_value 2 := by
    intro _ _ _ _
    exact ⟨by simp [Semantics]⟩
  true

end Semantics

namespace EnvironmentSemantics

#guard
  let _ : REPLSemantics empty_repl 4 := by
    intro name type binding
    simp at binding
  true

#guard
  let _ : REPLSemantics x_repl 1 := by
    simpa [x_repl, base_value] using
      (REPLSemantics.extend
        (repl := empty_repl)
        (fuel := 1)
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
  let _ : Semantics (Ty.base :=> Ty.base) (empty_repl.eval id_scoped) 2 := by
    exact fundamental empty_repl id_scoped (fuel := 2) (by
      intro name type binding
      simp at binding)
  true

#guard
  let _ : Semantics Ty.base (empty_repl.eval id_app_scoped) 2 := by
    exact fundamental empty_repl id_app_scoped (fuel := 2) (by
      intro name type binding
      simp at binding)
  true

end Fundamental

namespace Soundness

#guard
  let _ : Semantics (Ty.base :=> Ty.base) (REPL.empty.eval id_scoped) 2 :=
    soundness id_scoped 2
  true

#guard
  let _ : Semantics Ty.base (REPL.empty.eval id_app_scoped) 2 :=
    soundness id_app_scoped 2
  true

end Soundness

end Example

end STLC
