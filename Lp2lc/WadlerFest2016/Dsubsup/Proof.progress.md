# Dsubsup (D<:>) — Proof.progress

Track theorem and lemma statements from Coq `Lp2lc_coq/Active/Dsubsup.v` mirrored
in `Lp2lc/Active/Dsubsup/Proof.lean`. All proofs are `sorry` by policy.

Conventions
- Maintain original order as closely as practical; split mutual lemmas into `_T`/`_E` when convenient.
- Record status: yes/no for discharged proofs (initially all no).
- No axioms in this file; only theorem statements with `sorry` bodies.

Coverage Table (synchronized with current Proof.lean)

| Coq theorem name                    | Lean theorem name                      | proven | Category                |
|-------------------------------------|----------------------------------------|--------|-------------------------|
| preservation                        | preservation_result                    | no     | meta                    |
| progress                            | progress_result                        | no     | meta                    |
| open_rec_lc_core                    | open_rec_lc_core_T / open_rec_lc_core_E| no     | opening                 |
| open_rec_lc                         | open_rec_lc_T / open_rec_lc_E          | no     | opening                 |
| open_t_var_type                     | open_t_var_type                        | no     | opening                 |
| subst_fresh                         | subst_fresh_T / subst_fresh_E          | no     | substitution            |
| subst_open_rec                      | subst_open_rec_T / subst_open_rec_E    | no     | substitution            |
| subst_t_open_t                      | substT_openT                           | no     | substitution            |
| subst_e_open_e                      | substE_openE                           | no     | substitution            |
| subst_t_open_t_var                  | substT_openT_var                       | no     | substitution            |
| subst_e_open_e_var                  | substE_openE_var                       | no     | substitution            |
| subst_t_intro                       | substT_intro                           | no     | substitution            |
| subst_e_intro                       | substE_intro                           | no     | substitution            |
| subst_lc                            | subst_lc_T / subst_lc_E                | no     | regularity              |
| subst_t_type                        | substT_type                            | no     | regularity              |
| subst_e_term                        | substE_term                            | no     | regularity              |
| subst_e_value                       | substE_value                           | no     | regularity              |
| wft_lc                              | wft_lcT                                | no     | regularity              |
| wfe_lc                              | wfe_lcE                                | no     | regularity              |
| wft_type                            | wft_type                               | no     | regularity              |
| wfe_term                            | wfe_term                               | no     | regularity              |
| sub_reflexivity                     | sub_reflexivity                        | no     | subtyping               |
| sub_weakening                       | sub_weakening                          | no     | weakening               |
| sub_has_weakening                  | sub_has_weakening_pair                 | no     | weakening               |
| sub_weakening1                      | sub_weakening1                         | no     | weakening               |
| sub_weakening_empty                 | sub_weakening_empty                    | no     | weakening               |
| has_weakening                       | has_weakening                          | no     | weakening               |
| has_weakening1                      | has_weakening1                         | no     | weakening               |
| has_weakening_empty                 | has_weakening_empty                    | no     | weakening               |
| sub_narrowing                       | sub_narrowing                          | no     | narrowing               |
| sub_has_narrowing_aux              | sub_has_narrowing_aux                  | no     | narrowing               |
| sub_narrowing_empty                 | sub_narrowing_empty                    | no     | narrowing               |
| typing_weakening                    | typing_weakening                       | no     | weakening               |
| typing_narrowing                    | typing_narrowing                       | no     | narrowing               |
| typing_narrowing_empty              | typing_narrowing_empty                 | no     | narrowing               |
| typing_through_subst                | typing_through_subst                   | no     | substitution            |
| wf_weaken                           | wf_weaken_T / wf_weaken_E              | no     | weakening               |
| wft_weaken                          | wft_weaken                             | no     | weakening               |
| wft_weaken_empty                    | wft_weaken_empty                       | no     | weakening               |
| wfe_weaken                          | wfe_weaken                             | no     | weakening               |
| wfe_weaken_empty                    | wfe_weaken_empty                       | no     | weakening               |
| wf_narrow                           | wf_narrow_T / wf_narrow_E              | no     | narrowing               |
| wft_narrow                          | wft_narrow                             | no     | narrowing               |
| wf_subst                            | wf_subst_T / wf_subst_E                | no     | substitution            |
| wft_subst                           | wft_subst                              | no     | substitution            |
| wft_subst1                          | wft_subst1                             | no     | substitution            |
| wft_subst_empty                     | wft_subst_empty                        | no     | substitution            |
| notin_fv_open_rec                   | notin_fv_open_rec_T / _E               | no     | free-vars               |
| notin_fv_t_open                     | notin_fv_t_open                        | no     | free-vars               |
| notin_fv_e_open                     | notin_fv_e_open                        | no     | free-vars               |
| notin_fv_wf_rec                     | notin_fv_wf_rec_T / _E                 | no     | free-vars               |
| notin_fv_wf                         | notin_fv_wf                            | no     | free-vars               |
| map_subst_id                        | map_subst_id                           | no     | env/substitution        |
| ok_from_okt                         | ok_from_okt                            | no     | environment             |
| wft_from_env_has                    | wft_from_env_has                       | no     | environment             |
| okt_push_inv                        | okt_push_inv                           | no     | environment             |
| okt_push_type                       | okt_push_type                          | no     | environment             |
| okt_narrow                          | okt_narrow                             | no     | environment             |
| okt_subst                           | okt_subst                              | no     | environment             |
| okt_subst1                          | okt_subst1                             | no     | environment             |
| wft_from_okt                        | wft_from_okt                           | no     | environment             |
| wft_weaken_right                    | wft_weaken_right                       | no     | weakening               |
| sub_regular                         | sub_regular                            | no     | regularity              |
| has_regular                         | has_regular                            | no     | regularity              |
| has_regular_e                       | has_regular_e                          | no     | regularity              |
| typing_regular                      | typing_regular                         | no     | regularity              |
| value_regular                       | value_regular                          | no     | regularity              |
| red_regular                         | red_regular                            | no     | regularity              |
| wft_open                            | wft_open                               | no     | opening                 |
| has_value_var                       | has_value_var                          | no     | typing/meta             |
| sub_has_through_subst               | sub_has_through_subst                  | no     | substitution            |
| var_typing_has                      | var_typing_has                         | no     | typing                  |
| val_typing_has                      | val_typing_has                         | no     | typing                  |
| has_empty_value                     | has_empty_value                        | no     | regularity              |
| psub_sub                            | psub_sub                               | no     | subtyping               |
| possible_types_value                | possible_types_value                   | no     | canonical forms         |
| possible_types_wfe                  | possible_types_wfe                     | no     | canonical forms         |
| possible_types_wft                  | possible_types_wft                     | no     | canonical forms         |
| has_empty_var_false                 | has_empty_var_false                    | no     | regularity              |
| possible_types_closure_psub         | possible_types_closure_psub            | no     | canonical forms         |
| psub_reflexivity                    | psub_reflexivity                       | no     | subtyping               |
| sub_psub_aux                        | sub_psub_aux_sub / sub_psub_aux_has    | no     | subtyping               |
| sub_psub                            | sub_psub                               | no     | subtyping               |
| possible_types_closure              | possible_types_closure                 | no     | canonical forms         |
| possible_types_typing               | possible_types_typing                  | no     | canonical forms         |
| typing_inv_abs                      | typing_inv_abs                         | no     | inversion               |
| typing_through_subst1               | typing_through_subst1                  | no     | substitution            |
| value_red_contra                    | value_red_contra                       | no     | preservation helper     |
| canonical_form_abs                  | canonical_form_abs                     | no     | canonical forms         |
| canonical_form_mem                  | canonical_form_mem                     | no     | canonical forms         |

Notes
- This list follows the current order in Proof.lean, which preserves the Coq order (sections and lemma sequence), splitting mutual statements where appropriate.
- All proofs remain `sorry` by design (scaffold phase). No axioms are present in this file.

TODO
- If new lemmas are added to Proof.lean, append corresponding rows here immediately (maintaining order) and mark proven=no.
- If statement names change, update the table to stay in sync.
- When proofs are discharged later, flip proven to yes and, per project rule, move completed proofs into Lp2lc/Active/Fsub.lean while retaining statement ownership here.
