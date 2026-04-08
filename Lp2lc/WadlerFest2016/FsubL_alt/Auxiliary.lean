import Aesop
import «Lp2lc».Active.FsubL_alt.Def

namespace Lp2lc.Active.FsubL_alt

-- Aesop hints to mimic Coq `Hint Constructors`
-- These make constructor-style goals easier to solve during later proof work.
attribute [aesop safe] DefType.type_top
attribute [aesop safe] DefType.type_bot
attribute [aesop safe] DefType.type_var
attribute [aesop safe] DefType.type_arrow
attribute [aesop safe] DefType.type_all

attribute [aesop safe] DefTerm.term_var
attribute [aesop safe] DefTerm.term_abs
attribute [aesop safe] DefTerm.term_app
attribute [aesop safe] DefTerm.term_tabs
attribute [aesop safe] DefTerm.term_tapp

attribute [aesop safe] Wft.wft_top
attribute [aesop safe] Wft.wft_bot
attribute [aesop safe] Wft.wft_var
attribute [aesop safe] Wft.wft_arrow
attribute [aesop safe] Wft.wft_all

attribute [aesop safe] Okt.okt_empty
attribute [aesop safe] Okt.okt_sub
attribute [aesop safe] Okt.okt_typ

attribute [aesop safe] Value.value_abs
attribute [aesop safe] Value.value_tabs

attribute [aesop safe] Red.red_app_1
attribute [aesop safe] Red.red_app_2
attribute [aesop safe] Red.red_tapp
attribute [aesop safe] Red.red_abs
attribute [aesop safe] Red.red_tabs

-- Placeholder section for future tactic macros / utilities mirroring Coq Ltac.
-- TODO: add tactic macros if/when needed during proof implementation.

end Lp2lc.Active.FsubL_alt
