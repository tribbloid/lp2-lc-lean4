# Proof.progress (Ddia)

Coq file: Lp2lc_coq/Active/Ddia.v
All theorem/lemma statements to be scaffolded in Proof.lean (Proven? = no).

| Coq theorem name               | Lean theorem name          | Proven? | Category         |
|--------------------------------|----------------------------|---------|------------------|
| open_rec_lc_core               | open_rec_lc_core           | no      | opening          |
| open_rec_lc                    | open_rec_lc                | no      | opening          |
| open_t_var_type                | open_t_var_type            | no      | opening          |
| subst_fresh                    | subst_fresh                | no      | substitution     |
| subst_open_rec                 | subst_open_rec             | no      | substitution     |
| subst_t_open_t                 | subst_t_open_t             | no      | substitution     |
| subst_e_open_e                 | subst_e_open_e             | no      | substitution     |
| subst_t_open_t_var             | subst_t_open_t_var         | no      | substitution     |
| subst_e_open_e_var             | subst_e_open_e_var         | no      | substitution     |
| subst_t_intro                  | subst_t_intro              | no      | substitution     |
| subst_e_intro                  | subst_e_intro              | no      | substitution     |
|| subst_lc                       | subst_lc                   | no      | lc preservation  |
|| subst_t_type                   | subst_t_type               | no      | lc preservation  |
|| subst_e_term                   | subst_e_term               | no      | lc preservation  |
| subst_e_value                  | subst_e_value              | no      | lc preservation  |
| value_is_term                  | value_is_term              | yes     | regularity       |
|| wf_lc                          | wf_lc                      | no      | regularity       |
|| wft_type                       | wft_type                   | no      | regularity       |
|| wfe_term                       | wfe_term                   | no      | regularity       |
| wf_weaken                      | wf_weaken                  | no      | weakening        |
| wft_weaken                     | wft_weaken                 | no      | weakening        |
| wft_weaken_empty               | wft_weaken_empty           | no      | weakening        |
| wfe_weaken                     | wfe_weaken                 | no      | weakening        |
| wfe_weaken_empty               | wfe_weaken_empty           | no      | weakening        |
| wf_narrow                      | wf_narrow                  | no      | narrowing        |
| wft_narrow                     | wft_narrow                 | no      | narrowing        |
| wf_subst                       | wf_subst                   | no      | substitution     |
| wft_subst                      | wft_subst                  | no      | substitution     |
| wft_subst1                     | wft_subst1                 | no      | substitution     |
| wft_subst_empty                | wft_subst_empty            | no      | substitution     |
| wft_open                       | wft_open                   | no      | opening          |
| ok_from_okt                    | ok_from_okt                | no      | env              |
| wft_from_env_has               | wft_from_env_has           | no      | env              |
| wft_from_okt                   | wft_from_okt               | no      | env              |
| wft_weaken_right               | wft_weaken_right           | no      | weakening        |
| okt_push_inv                   | okt_push_inv               | no      | env              |
| okt_push_type                  | okt_push_type              | no      | env              |
| okt_narrow                     | okt_narrow                 | no      | env              |
| okt_subst                      | okt_subst                  | no      | env              |
| okt_subst1                     | okt_subst1                 | no      | env              |
| notin_fv_open_rec              | notin_fv_open_rec          | no      | fv               |
| notin_fv_t_open                | notin_fv_t_open            | no      | fv               |
| notin_fv_e_open                | notin_fv_e_open            | no      | fv               |
| notin_fv_wf_rec                | notin_fv_wf_rec            | no      | fv               |
| notin_fv_wf                    | notin_fv_wf                | no      | fv               |
| map_subst_id                   | map_subst_id               | no      | env              |
| sub_has_regular                | sub_has_regular            | no      | regularity       |
| sub_regular                    | sub_regular                | no      | regularity       |
| has_regular                    | has_regular                | no      | regularity       |
| has_regular_e                  | has_regular_e              | no      | regularity       |
| typing_regular                 | typing_regular             | no      | regularity       |
| value_regular                  | value_regular              | no      | regularity       |
| red_regular                    | red_regular                | no      | regularity       |
| sub_reflexivity                | sub_reflexivity            | no      | subtyping        |
| sub_has_weakening              | sub_has_weakening          | no      | weakening        |
| sub_weakening                  | sub_weakening              | no      | weakening        |
| sub_weakening1                 | sub_weakening1             | no      | weakening        |
| sub_weakening_empty            | sub_weakening_empty        | no      | weakening        |
| has_weakening                  | has_weakening              | no      | weakening        |
| has_weakening1                 | has_weakening1             | no      | weakening        |
| has_weakening_empty            | has_weakening_empty        | no      | weakening        |
| sub_has_narrowing_aux          | sub_has_narrowing_aux      | no      | narrowing        |
| sub_narrowing                  | sub_narrowing              | no      | narrowing        |
| sub_narrowing_empty            | sub_narrowing_empty        | no      | narrowing        |
| has_value_var                  | has_value_var              | no      | typing/has       |
| var_typing_has                 | var_typing_has             | no      | typing/has       |
| val_typing_has                 | val_typing_has             | no      | typing/has       |
| sub_has_through_subst          | sub_has_through_subst      | no      | substitution     |
| typing_weakening               | typing_weakening           | no      | weakening        |
| typing_narrowing               | typing_narrowing           | no      | narrowing        |
| typing_narrowing_empty         | typing_narrowing_empty     | no      | narrowing        |
| typing_through_subst           | typing_through_subst       | no      | substitution     |
| has_empty_value                | has_empty_value            | no      | value/has        |
| psub_sub                       | psub_sub                   | no      | aux-subtyping    |
| possible_types_value           | possible_types_value       | no      | canonical forms  |
| possible_types_wfe             | possible_types_wfe         | no      | canonical forms  |
| possible_types_wft             | possible_types_wft         | no      | canonical forms  |
| has_empty_var_false            | has_empty_var_false        | no      | env             |
| possible_types_closure_psub    | possible_types_closure_psub| no      | closure          |
| psub_reflexivity               | psub_reflexivity           | no      | closure          |
| sub_psub_aux                   | sub_psub_aux               | no      | closure          |
| sub_psub                       | sub_psub                   | no      | closure          |
| possible_types_closure         | possible_types_closure     | no      | closure          |
| possible_types_typing          | possible_types_typing      | no      | canonical forms  |
| typing_inv_abs                 | typing_inv_abs             | no      | inversion        |
| canonical_form_abs             | canonical_form_abs         | no      | canonical forms  |
| canonical_form_mem             | canonical_form_mem         | no      | canonical forms  |
| typing_through_subst1          | typing_through_subst1      | no      | substitution     |
|| value_red_contra               | value_red_contra           | no      | reduction        |
| preservation_result            | preservation_result        | no      | preservation     |
| progress_result                | progress_result            | no      | progress         |

Notes:
- This table is comprehensive for Ddia.v; as stubs are added to Proof.lean, keep this list in-sync.
- All entries are currently unproven (scaffold step).
