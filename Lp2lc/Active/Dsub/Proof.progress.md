# Dsub Proof.progress.md

Track all lemmas and theorems from Coq Lp2lc_coq/Active/Dsub.v. Maintain source order.

| Coq theorem name | Lean theorem name | proven? | Category |
|---|---|---|---|
| open_rec_lc_core (type part) | open_rec_lc_core_t | no | substitution/opening |
| open_rec_lc_core (term part) | open_rec_lc_core_e | no | substitution/opening |
| open_rec_lc (type part) | open_rec_lc_t | no | local closure |
| open_rec_lc (term part) | open_rec_lc_e | no | local closure |
| open_t_var_type | open_t_var_type | no | local closure |
| subst_fresh (type) | subst_fresh_t | no | substitution |
| subst_fresh (term) | subst_fresh_e | no | substitution |
| value_is_term | value_is_term | no | regularity |
| wf_lc (type part) | wf_lc_t | no | regularity |
| wf_lc (term part) | wf_lc_e | no | regularity |
| wft_type | wft_type | no | regularity |
| wfe_term | wfe_term | no | regularity |
| wft_weaken | wft_weaken | no | structural |
| wfe_weaken | wfe_weaken | no | structural |
| ok_from_okt | ok_from_okt | no | env |
| wft_from_okt | wft_from_okt | no | env |
| wft_weaken_right | wft_weaken_right | no | structural |
| sub_regular | sub_regular | no | regularity |
| has_regular | has_regular | no | regularity |
| has_regular_e | has_regular_e | no | regularity |
| typing_regular | typing_regular | no | regularity |
| value_regular | value_regular | no | regularity |
| red_regular | red_regular | no | regularity |
| sub_reflexivity | sub_reflexivity | no | sub |
| sub_weakening | sub_weakening | no | sub |
| has_weakening | has_weakening | no | has |
| typing_weakening | typing_weakening | no | typing |
| typing_narrowing | typing_narrowing | no | typing |
| typing_narrowing_empty | typing_narrowing_empty | no | typing |
| typing_through_subst | typing_through_subst | no | typing |
| canonical_form_abs | canonical_form_abs | no | canonical |
| canonical_form_mem | canonical_form_mem | no | canonical |
| typing_through_subst1 | typing_through_subst1 | no | typing |
| value_red_contra | value_red_contra | no | reduction |
| preservation_result | preservation_result | no | preservation |
| progress_result | progress_result | no | progress |
| subst_open_rec (type) | subst_open_rec_t | no | substitution |
| subst_open_rec (term) | subst_open_rec_e | no | substitution |
| subst_t_open_t | subst_t_open_t | no | substitution |
| subst_e_open_e | subst_e_open_e | no | substitution |
| subst_t_open_t_var | subst_t_open_t_var | no | substitution |
| subst_e_open_e_var | subst_e_open_e_var | no | substitution |
| subst_t_intro | subst_t_intro | no | substitution |
| subst_e_intro | subst_e_intro | no | substitution |
| subst_lc (type) | subst_lc_t | no | substitution |
| subst_lc (term) | subst_lc_e | no | substitution |
| subst_e_value | subst_e_value | no | substitution |
| notin_fv_open_rec (type) | notin_fv_open_rec_t | no | fv |
| notin_fv_open_rec (term) | notin_fv_open_rec_e | no | fv |
| notin_fv_t_open | notin_fv_t_open | no | fv |
| notin_fv_e_open | notin_fv_e_open | no | fv |
| notin_fv_wf (type) | notin_fv_wf_t | no | fv/env |
| notin_fv_wf (term) | notin_fv_wf_e | no | fv/env |
| notin_fv_wf (corollary) | notin_fv_wf | no | fv/env |
| map_subst_t_id | map_subst_t_id | no | env |
| binds_weaken | binds_weaken | no | env |
| wft_weaken_empty | wft_weaken_empty | no | env |
| wfe_weaken_empty | wfe_weaken_empty | no | env |
| wf_narrow (type) | wf_narrow_t | no | env |
| wf_narrow (term) | wf_narrow_e | no | env |
| wft_narrow | wft_narrow | no | env |
| wf_subst (type) | wf_subst_t | no | env |
| wf_subst (term) | wf_subst_e | no | env |
| wft_subst | wft_subst | no | env |
| wft_subst1 | wft_subst1 | no | env |
| wft_subst_empty | wft_subst_empty | no | env |
| wft_open | wft_open | no | env |
| okt_push_inv | okt_push_inv | no | env |
| okt_push_type | okt_push_type | no | env |
| okt_narrow | okt_narrow | no | env |
| okt_strengthen | okt_strengthen | no | env |
| okt_subst | okt_subst | no | env |
| okt_subst1 | okt_subst1 | no | env |
| sub_weakening1 | sub_weakening1 | no | sub |
| sub_weakening_empty | sub_weakening_empty | no | sub |
| has_weakening1 | has_weakening1 | no | has |
| has_weakening_empty | has_weakening_empty | no | has |
| sub_has_narrowing_aux (sub) | sub_has_narrowing_aux_t | no | sub |
| sub_has_narrowing_aux (has) | sub_has_narrowing_aux_e | no | has |
| sub_narrowing | sub_narrowing | no | sub |
| sub_narrowing_empty | sub_narrowing_empty | no | sub |
| has_value_var | has_value_var | no | has |
| var_typing_has | var_typing_has | no | has/typing |
| val_typing_has | val_typing_has | no | has/typing |
| sub_has_through_subst (sub) | sub_has_through_subst_t | no | sub |
| sub_has_through_subst (has) | sub_has_through_subst_e | no | has |
| has_empty_value | has_empty_value | no | has |
| psub_sub | psub_sub | no | psub |
| possible_types_value | possible_types_value | no | ptypes |
| possible_types_wfe | possible_types_wfe | no | ptypes |
| possible_types_wft | possible_types_wft | no | ptypes |
| has_empty_var_false | has_empty_var_false | no | has |
| possible_types_closure_psub | possible_types_closure_psub | no | ptypes |
| psub_reflexivity | psub_reflexivity | no | psub |
| sub_psub_aux (sub) | sub_psub_aux_t | no | psub |
| sub_psub_aux (has) | sub_psub_aux_e | no | ptypes |
| sub_psub | sub_psub | no | psub |
| possible_types_closure | possible_types_closure | no | ptypes |
| possible_types_typing | possible_types_typing | no | ptypes |
| typing_inv_abs | typing_inv_abs | no | typing |
