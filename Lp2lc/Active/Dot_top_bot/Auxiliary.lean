import Std
import Aesop
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Dot_top_bot.Def

namespace Lp2lc.Active.Dot_top_bot

open Aesop

-- Register constructors to emulate Coq Hint Constructors
attribute [aesop safe] Label.label_typ Label.label_trm
attribute [aesop safe] Avar.avar_b Avar.avar_f
attribute [aesop safe] Typ.typ_top Typ.typ_bot
attribute [aesop safe] Typ.typ_rcd Typ.typ_and Typ.typ_sel Typ.typ_bnd Typ.typ_all
attribute [aesop safe] Dec.dec_typ Dec.dec_trm
attribute [aesop safe] Trm.trm_var Trm.trm_val Trm.trm_sel Trm.trm_app Trm.trm_let
attribute [aesop safe] Val.val_new Val.val_lambda
attribute [aesop safe] Defn.def_typ Defn.def_trm
attribute [aesop safe] Defs.defs_nil Defs.defs_cons

attribute [aesop safe] Red.red_sel Red.red_app Red.red_let Red.red_let_var Red.red_let_tgt

attribute [aesop safe] TyTrm.ty_var TyTrm.ty_all_intro TyTrm.ty_all_elim
attribute [aesop safe] TyTrm.ty_new_intro TyTrm.ty_new_elim TyTrm.ty_let
attribute [aesop safe] TyTrm.ty_rec_intro TyTrm.ty_rec_elim TyTrm.ty_and_intro TyTrm.ty_sub
attribute [aesop safe] TyDef.ty_def_typ TyDef.ty_def_trm
attribute [aesop safe] TyDefs.ty_defs_one TyDefs.ty_defs_cons

attribute [aesop safe] Subtyp.subtyp_top Subtyp.subtyp_bot Subtyp.subtyp_refl Subtyp.subtyp_trans
attribute [aesop safe] Subtyp.subtyp_and11 Subtyp.subtyp_and12 Subtyp.subtyp_and2 Subtyp.subtyp_fld
attribute [aesop safe] Subtyp.subtyp_typ Subtyp.subtyp_sel2 Subtyp.subtyp_sel1
attribute [aesop safe] Subtyp.subtyp_sel2_tight Subtyp.subtyp_sel1_tight Subtyp.subtyp_all


attribute [aesop safe] RecordDec.rd_typ RecordDec.rd_trm
attribute [aesop safe] RecordTyp.rt_one RecordTyp.rt_cons

  attribute [aesop safe] HasMember.has_any
  attribute [aesop safe] HasMemberRules.has_refl HasMemberRules.has_and1 HasMemberRules.has_and2
  attribute [aesop safe] HasMemberRules.has_bnd HasMemberRules.has_sel

-- Environment relation used by narrowing (Coq: subenv)
  def subenv (G1 G2 : Ctx) : Prop :=
    ∀ (x : Var) (T2 : Typ),
      Env.binds x T2 G2 →
        Env.binds x T2 G1 ∨
        ∃ T1 : Typ, Env.binds x T1 G1 ∧ Subtyp Tymode.ty_general Submode.sub_general G1 T1 T2
