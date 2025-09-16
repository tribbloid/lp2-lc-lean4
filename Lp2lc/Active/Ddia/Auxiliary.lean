import Std
import Mathlib.Data.Finset.Basic
import Aesop
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Ddia.Def

namespace Lp2lc.Active.Ddia

open def_type def_term wft wfe okt value red typing typ trm

/- Aesop hints to mimic Coq `Hint Constructors` (no axioms). -/
attribute [aesop safe] def_type.type_bot
attribute [aesop safe] def_type.type_top
attribute [aesop safe] def_type.type_and
attribute [aesop safe] def_type.type_or
attribute [aesop safe] def_type.type_sel
attribute [aesop safe] def_type.type_mem
attribute [aesop safe] def_type.type_all

attribute [aesop safe] def_term.term_var
attribute [aesop safe] def_term.term_abs
attribute [aesop safe] def_term.term_mem
attribute [aesop safe] def_term.term_app

attribute [aesop safe] value.value_abs
attribute [aesop safe] value.value_mem

attribute [aesop safe] wft.wft_bot
attribute [aesop safe] wft.wft_top
attribute [aesop safe] wft.wft_and
attribute [aesop safe] wft.wft_or
attribute [aesop safe] wft.wft_sel
attribute [aesop safe] wft.wft_mem
attribute [aesop safe] wft.wft_all

attribute [aesop safe] wfe.wfe_var
attribute [aesop safe] wfe.wfe_abs
attribute [aesop safe] wfe.wfe_mem
attribute [aesop safe] wfe.wfe_app

attribute [aesop safe] okt.okt_empty
attribute [aesop safe] okt.okt_push

attribute [aesop safe] sub.sub_bot
attribute [aesop safe] sub.sub_top
attribute [aesop safe] sub.sub_and11
attribute [aesop safe] sub.sub_and12
attribute [aesop safe] sub.sub_and2
attribute [aesop safe] sub.sub_or21
attribute [aesop safe] sub.sub_or22
attribute [aesop safe] sub.sub_or1
attribute [aesop safe] sub.sub_refl_sel
attribute [aesop safe] sub.sub_sel1
attribute [aesop safe] sub.sub_sel2
attribute [aesop safe] sub.sub_mem
attribute [aesop safe] sub.sub_all
attribute [aesop safe] sub.sub_trans

attribute [aesop safe] has.has_var
attribute [aesop safe] has.has_mem
attribute [aesop safe] has.has_abs
attribute [aesop safe] has.has_sub

attribute [aesop safe] typing.typing_var
attribute [aesop safe] typing.typing_abs
attribute [aesop safe] typing.typing_mem
attribute [aesop safe] typing.typing_app
attribute [aesop safe] typing.typing_appvar
attribute [aesop safe] typing.typing_sub

attribute [aesop safe] red.red_app_1
attribute [aesop safe] red.red_app_2
attribute [aesop safe] red.red_abs

/- Placeholder for tactic macros mirroring Coq Ltac (optional later). -/
-- TODO: add tactic macros like `apply_fresh` if needed.

end Lp2lc.Active.Ddia
