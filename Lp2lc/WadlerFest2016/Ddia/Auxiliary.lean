import Std
import Mathlib.Data.Finset.Basic

import Aesop
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Ddia.Def

namespace Lp2lc.Active.Ddia

/- Aesop hints to mimic Coq `Hint Constructors` (no axioms). -/
attribute [aesop safe] DefType.type_bot
attribute [aesop safe] DefType.type_top
attribute [aesop safe] DefType.type_and
attribute [aesop safe] DefType.type_or
attribute [aesop safe] DefType.type_sel
attribute [aesop safe] DefType.type_mem
attribute [aesop safe] DefType.type_all

attribute [aesop safe] DefTerm.term_var
attribute [aesop safe] DefTerm.term_abs
attribute [aesop safe] DefTerm.term_mem
attribute [aesop safe] DefTerm.term_app

attribute [aesop safe] Value.value_abs
attribute [aesop safe] Value.value_mem

attribute [aesop safe] Wft.wft_bot
attribute [aesop safe] Wft.wft_top
attribute [aesop safe] Wft.wft_and
attribute [aesop safe] Wft.wft_or
attribute [aesop safe] Wft.wft_sel
attribute [aesop safe] Wft.wft_mem
attribute [aesop safe] Wft.wft_all

attribute [aesop safe] Wfe.wfe_var
attribute [aesop safe] Wfe.wfe_abs
attribute [aesop safe] Wfe.wfe_mem
attribute [aesop safe] Wfe.wfe_app

attribute [aesop safe] Okt.okt_empty
attribute [aesop safe] Okt.okt_push

attribute [aesop safe] Sub.sub_bot
attribute [aesop safe] Sub.sub_top
attribute [aesop safe] Sub.sub_and11
attribute [aesop safe] Sub.sub_and12
attribute [aesop safe] Sub.sub_and2
attribute [aesop safe] Sub.sub_or21
attribute [aesop safe] Sub.sub_or22
attribute [aesop safe] Sub.sub_or1
attribute [aesop safe] Sub.sub_refl_sel
attribute [aesop safe] Sub.sub_sel1
attribute [aesop safe] Sub.sub_sel2
attribute [aesop safe] Sub.sub_mem
attribute [aesop safe] Sub.sub_all
attribute [aesop safe] Sub.sub_trans

attribute [aesop safe] Has.has_var
attribute [aesop safe] Has.has_mem
attribute [aesop safe] Has.has_abs
attribute [aesop safe] Has.has_sub

attribute [aesop safe] Typing.typing_var
attribute [aesop safe] Typing.typing_abs
attribute [aesop safe] Typing.typing_mem
attribute [aesop safe] Typing.typing_app
attribute [aesop safe] Typing.typing_appvar
attribute [aesop safe] Typing.typing_sub

attribute [aesop safe] Red.red_app_1
attribute [aesop safe] Red.red_app_2
attribute [aesop safe] Red.red_abs

/- Placeholder for tactic macros mirroring Coq Ltac (optional later). -/
-- TODO: add tactic macros like `apply_fresh` if needed.

end Lp2lc.Active.Ddia
