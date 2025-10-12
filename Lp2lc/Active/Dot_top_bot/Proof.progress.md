# Proof.progress.md — Dot_top_bot

List of Coq lemmas/theorems and their Lean counterparts in `Lp2lc/Active/Dot_top_bot/Proof.lean`.

Columns:
- Coq theorem name
- Lean theorem name
- Discharged (yes/no)
- Category (full name)

| Coq theorem name | Lean theorem name | Discharged | Category |
|---|---|---|---|
| fresh_push_eq_inv | fresh_push_eq_inv | yes | Infrastructure |
| weaken_rules | weaken_rules | no | Weakening |
| weaken_ty_trm | weaken_ty_trm | no | Weakening |
| weaken_subtyp | weaken_subtyp | no | Weakening |
| wf_sto_to_ok_s | wf_sto_to_ok_s | no | Well-formed store |
| wf_sto_to_ok_G | wf_sto_to_ok_G | no | Well-formed store |
| ctx_binds_to_sto_binds_raw | ctx_binds_to_sto_binds_raw | no | Store-context relations |
| sto_binds_to_ctx_binds_raw | sto_binds_to_ctx_binds_raw | no | Store-context relations |
| invert_wf_sto_concat | invert_wf_sto_concat | no | Store-context relations |
| sto_unbound_to_ctx_unbound | sto_unbound_to_ctx_unbound | no | Store-context relations |
| ctx_unbound_to_sto_unbound | ctx_unbound_to_sto_unbound | no | Store-context relations |
| typing_implies_bound | typing_implies_bound | no | Typing inversion |
| typing_bvar_implies_false | typing_bvar_implies_false | no | Typing inversion |
| extra_bnd_rules | extra_bnd_rules | no | Extra Rec |
| subst_fresh_avar | subst_fresh_avar | no | Substitution (freshness) |
| subst_fresh_typ_dec | subst_fresh_typ_dec | no | Substitution (freshness) |
| subst_fresh_trm_val_def_defs | subst_fresh_trm_val_def_defs | no | Substitution (freshness) |
| invert_fv_ctx_types_push | invert_fv_ctx_types_push | no | Free variables |
| subst_fresh_ctx | subst_fresh_ctx | no | Substitution (contexts) |
| subst_open_commute_avar | subst_open_commute_avar | no | Substitution (commuting) |
| subst_open_commute_typ_dec | subst_open_commute_typ_dec | no | Substitution (commuting) |
| subst_open_commute_typ | subst_open_commute_typ | no | Substitution (commuting) |
| subst_open_commute_dec | subst_open_commute_dec | no | Substitution (commuting) |
| subst_open_commute_trm_val_def_defs | subst_open_commute_trm_val_def_defs | no | Substitution (commuting) |
| subst_open_commute_trm | subst_open_commute_trm | no | Substitution (commuting) |
| subst_open_commute_val | subst_open_commute_val | no | Substitution (commuting) |
| subst_open_commute_defs | subst_open_commute_defs | no | Substitution (commuting) |
| subst_intro_trm | subst_intro_trm | no | Substitution (intro) |
| subst_intro_val | subst_intro_val | no | Substitution (intro) |
| subst_intro_defs | subst_intro_defs | no | Substitution (intro) |
| subst_intro_typ | subst_intro_typ | no | Substitution (intro) |
| subst_intro_dec | subst_intro_dec | no | Substitution (intro) |
| subst_undo_avar | subst_undo_avar | no | Substitution (undo) |
| subst_undo_typ_dec | subst_undo_typ_dec | no | Substitution (undo) |
| subst_undo_trm_val_def_defs | subst_undo_trm_val_def_defs | no | Substitution (undo) |
| subst_typ_undo | subst_typ_undo | no | Substitution (undo) |
| subst_trm_undo | subst_trm_undo | no | Substitution (undo) |
| subst_idempotent_avar | subst_idempotent_avar | no | Substitution (idempotence) |
| subst_idempotent_typ_dec | subst_idempotent_typ_dec | no | Substitution (idempotence) |
| subst_idempotent_trm_val_def_defs | subst_idempotent_trm_val_def_defs | no | Substitution (idempotence) |
| subst_typ_idempotent | subst_typ_idempotent | no | Substitution (idempotence) |
| subst_trm_idempotent | subst_trm_idempotent | no | Substitution (idempotence) |
| subst_label_of_dec | subst_label_of_dec | no | Records (labels) |
| subst_label_of_def | subst_label_of_def | no | Records (labels) |
| subst_defs_hasnt | subst_defs_hasnt | no | Records (defs) |
| subst_rules | subst_rules | no | Substitution principle |
| subst_ty_trm | subst_ty_trm | no | Substitution principle |
| subst_ty_defs | subst_ty_defs | no | Substitution principle |
| corresponding_types | corresponding_types | no | Store-context relations |
| unique_rec_subtyping | unique_rec_subtyping | no | Subtyping uniqueness |
| unique_all_subtyping | unique_all_subtyping | no | Subtyping uniqueness |
| unique_lambda_typing | unique_lambda_typing | no | Typing inversion |
| lambda_not_rcd | lambda_not_rcd | no | Typing inversion |
| open_dec_preserves_label | open_dec_preserves_label | no | Records/open |
| open_record_dec | open_record_dec | no | Records/open |
| open_record_typ | open_record_typ | no | Records/open |
| open_eq_avar | open_eq_avar | no | Opening equality |
| open_eq_typ_dec | open_eq_typ_dec | no | Opening equality |
| open_eq_typ | open_eq_typ | no | Opening equality |
| open_record_dec_rev | open_record_dec_rev | no | Records/open |
| open_record_typ_rev | open_record_typ_rev | no | Records/open |
| open_record_type | open_record_type | no | Records/open |
| open_record_type_rev | open_record_type_rev | no | Records/open |
| label_same_typing | label_same_typing | no | Records/typing |
| record_defs_typing_rec | record_defs_typing_rec | no | Records/typing |
| record_defs_typing | record_defs_typing | no | Records/typing |
| record_new_typing | record_new_typing | no | Records/typing |
| subenv_push | subenv_push | no | Narrowing |
| subenv_last | subenv_last | no | Narrowing |
| narrow_rules | narrow_rules | no | Narrowing |
| narrow_typing | narrow_typing | no | Narrowing |
| narrow_subtyping | narrow_subtyping | no | Narrowing |
| has_member_rules_inv | has_member_rules_inv | no | Has-member inversion |
| has_member_inv | has_member_inv | no | Has-member inversion |
| has_member_covariance | has_member_covariance | no | Has-member |
| has_member_monotonicity | has_member_monotonicity | no | Has-member |
| val_new_typing | val_new_typing | no | Typing/values |
| record_typ_sub_closed | record_typ_sub_closed | no | Record-sub |
| record_type_sub_closed | record_type_sub_closed | no | Record-sub |
| record_sub_trans | record_sub_trans | no | Record-sub |
| record_subtyping | record_subtyping | no | Record-sub |
| record_typ_sub_label_in | record_typ_sub_label_in | no | Record-sub |
| rcd_typ_eq_bounds | rcd_typ_eq_bounds | no | Record-sub |
| unique_rcd_typ | unique_rcd_typ | no | Record-sub |
| record_type_sub_not_rec | record_type_sub_not_rec | no | Record-sub |
| shape_new_typing | shape_new_typing | no | Record-sub |
| unique_tight_bounds | unique_tight_bounds | no | Tight bounds |
| record_type_new | record_type_new | no | Records/store |
| has_member_rcd_typ_sub2_mut | has_member_rcd_typ_sub2_mut | no | Has-member/record-type |
| wf_sto_val_new_in_G | wf_sto_val_new_in_G | no | Store-context relations |
| tight_bound_completeness | tight_bound_completeness | no | Tight bound completeness |
| all_intro_inversion | all_intro_inversion | no | Canonical forms |
| new_intro_inversion | new_intro_inversion | no | Canonical forms |
| possible_types_closure_tight | possible_types_closure_tight | no | Possible types |
| precise_to_general | precise_to_general | no | Mode conversions |
| precise_to_general_typing | precise_to_general_typing | no | Mode conversions |
| tight_to_general | tight_to_general | no | Mode conversions |
| tight_to_general_typing | tight_to_general_typing | no | Mode conversions |
| tight_to_general_subtyping | tight_to_general_subtyping | no | Mode conversions |
| precise_to_tight | precise_to_tight | no | Mode conversions |
| precise_to_tight_typing | precise_to_tight_typing | no | Mode conversions |
| sto_binds_to_ctx_binds | sto_binds_to_ctx_binds | no | Store-context relations |
| ctx_binds_to_sto_binds | ctx_binds_to_sto_binds | no | Store-context relations |
| var_new_typing | var_new_typing | no | Records/typing |
| new_ty_defs | new_ty_defs | no | Records/typing |
| possible_types_closure | possible_types_closure | no | Possible types |
| var_typing_implies_avar_f | var_typing_implies_avar_f | no | Typing inversion |
| val_typing | val_typing | no | Typing/values |
| safety | safety | no | Safety |

Notes:
- Maintain original order as in Coq where possible; this table currently covers the subset scaffolded in `Proof.lean`. More entries will be appended as scaffolding proceeds across the file.
