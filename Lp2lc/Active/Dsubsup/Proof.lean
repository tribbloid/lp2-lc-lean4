import «Lp2lc».Active.Dsubsup.Def
import «Lp2lc».Active.Dsubsup.Auxiliary

namespace Lp2lc.Active.Dsubsup

open typ trm

-- Minimal early lemmas scaffolding (fill later)
@[simp] theorem open_rec_lc_core :
  (∀ T j v u i, i ≠ j → open_t_rec j v T = open_t_rec i u (open_t_rec j v T) → T = open_t_rec i u T) ∧
  (∀ e j v u i, i ≠ j → open_e_rec j v e = open_e_rec i u (open_e_rec j v e) → e = open_e_rec i u e) := by
  sorry

@[simp] theorem open_rec_lc :
  (∀ T, def_type T → ∀ u k, T = open_t_rec k u T) ∧ (∀ e, def_term e → ∀ u k, e = open_e_rec k u e) := by
  sorry

@[simp] theorem subst_fresh :
  (∀ T z u, z ∉ fv_t T → subst_t z u T = T) ∧ (∀ e z u, z ∉ fv_e e → subst_e z u e = e) := by
  sorry

end Lp2lc.Active.Dsubsup
