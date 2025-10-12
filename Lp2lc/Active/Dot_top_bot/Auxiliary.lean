import Std
import Aesop
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Dot_top_bot.Def

namespace Lp2lc.Active.Dot_top_bot

open Aesop

-- Register constructors to emulate Coq Hint Constructors
attribute [aesop safe] label.label_typ label.label_trm
attribute [aesop safe] avar.avar_b avar.avar_f
attribute [aesop safe] typ.typ_top typ.typ_bot
attribute [aesop safe] typ.typ_rcd typ.typ_and typ.typ_sel typ.typ_bnd typ.typ_all
attribute [aesop safe] dec.dec_typ dec.dec_trm
attribute [aesop safe] trm.trm_var trm.trm_val trm.trm_sel trm.trm_app trm.trm_let
attribute [aesop safe] val.val_new val.val_lambda
attribute [aesop safe] defn.def_typ defn.def_trm
attribute [aesop safe] defs.defs_nil defs.defs_cons

attribute [aesop safe] red.red_sel red.red_app red.red_let red.red_let_var red.red_let_tgt

attribute [aesop safe] ty_trm.ty_var ty_trm.ty_all_intro ty_trm.ty_all_elim
attribute [aesop safe] ty_trm.ty_new_intro ty_trm.ty_new_elim ty_trm.ty_let
attribute [aesop safe] ty_trm.ty_rec_intro ty_trm.ty_rec_elim ty_trm.ty_and_intro ty_trm.ty_sub
attribute [aesop safe] ty_def.ty_def_typ ty_def.ty_def_trm
attribute [aesop safe] ty_defs.ty_defs_one ty_defs.ty_defs_cons

attribute [aesop safe] subtyp.subtyp_top subtyp.subtyp_bot subtyp.subtyp_refl subtyp.subtyp_trans
attribute [aesop safe] subtyp.subtyp_and11 subtyp.subtyp_and12 subtyp.subtyp_and2 subtyp.subtyp_fld
attribute [aesop safe] subtyp.subtyp_typ subtyp.subtyp_sel2 subtyp.subtyp_sel1
attribute [aesop safe] subtyp.subtyp_sel2_tight subtyp.subtyp_sel1_tight subtyp.subtyp_all


attribute [aesop safe] record_dec.rd_typ record_dec.rd_trm
attribute [aesop safe] record_typ.rt_one record_typ.rt_cons

  attribute [aesop safe] has_member.has_any
  attribute [aesop safe] has_member_rules.has_refl has_member_rules.has_and1 has_member_rules.has_and2
  attribute [aesop safe] has_member_rules.has_bnd has_member_rules.has_sel

-- Environment relation used by narrowing (Coq: subenv)
  def subenv (G1 G2 : ctx) : Prop :=
    ∀ (x : Var) (T2 : typ),
      Env.binds x T2 G2 →
        Env.binds x T2 G1 ∨
        ∃ T1 : typ, Env.binds x T1 G1 ∧ subtyp tymode.ty_general submode.sub_general G1 T1 T2
