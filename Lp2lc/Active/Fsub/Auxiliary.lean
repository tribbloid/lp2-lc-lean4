import Std
import Mathlib.Data.Finset.Basic
import Aesop
import «Lp2lc».Shared
import «Lp2lc».Active.Fsub.Def

namespace Lp2lc.Active.Fsub

open def_type def_term wft okt value red typ trm bind

-- Aesop hints to mimic Coq `Hint Constructors`
-- These make constructor-style goals easier to solve during later proof work.
attribute [aesop safe] def_type.type_top
attribute [aesop safe] def_type.type_var
attribute [aesop safe] def_type.type_arrow
attribute [aesop safe] def_type.type_all

attribute [aesop safe] def_term.term_var
attribute [aesop safe] def_term.term_abs
attribute [aesop safe] def_term.term_app
attribute [aesop safe] def_term.term_tabs
attribute [aesop safe] def_term.term_tapp

attribute [aesop safe] wft.wft_top
attribute [aesop safe] wft.wft_var
attribute [aesop safe] wft.wft_arrow
attribute [aesop safe] wft.wft_all

attribute [aesop safe] okt.okt_empty
attribute [aesop safe] okt.okt_sub
attribute [aesop safe] okt.okt_typ

attribute [aesop safe] value.value_abs
attribute [aesop safe] value.value_tabs

attribute [aesop safe] red.red_app_1
attribute [aesop safe] red.red_app_2
attribute [aesop safe] red.red_tapp
attribute [aesop safe] red.red_abs
attribute [aesop safe] red.red_tabs

-- Placeholder section for future tactic macros / utilities mirroring Coq Ltac.
-- TODO: add tactic macros if/when needed during proof implementation.

end Lp2lc.Active.Fsub
