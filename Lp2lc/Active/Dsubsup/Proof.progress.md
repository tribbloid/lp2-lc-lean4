# Dsubsup (D<:>) — Proof.progress

Track theorem and lemma statements from Coq `Lp2lc_coq/Active/Dsubsup.v` mirrored
in `Lp2lc/Active/Dsubsup/Proof.lean`. All proofs are `sorry` by policy.

Conventions
- Maintain original order as closely as practical.
- Record status: yes/no for discharged proofs (initially all no).

Coverage Table (initial subset)

| Coq theorem name           | Lean theorem name        | proven | Category              |
|----------------------------|--------------------------|--------|-----------------------|
| preservation (packaged)    | preservation_result      | no     | meta-property         |
| progress (packaged)        | progress_result          | no     | meta-property         |
| subst_t_open_t             | substT_openT             | no     | substitution property |
| subst_e_open_e             | substE_openE             | no     | substitution property |
| wft_lc                     | wft_lcT                  | no     | regularity            |
| wfe_lc                     | wfe_lcE                  | no     | regularity            |
| sub_weakening              | sub_weakening            | no     | structural            |
| typing_narrowing           | typing_narrowing         | no     | structural            |
| typing_through_subst       | typing_through_subst     | no     | structural            |
| canonical_form_abs         | canonical_form_abs       | no     | canonical forms       |
| canonical_form_mem         | canonical_form_mem       | no     | canonical forms       |

Additional Coq lemmas (pending scaffolds; all unproven)

| Coq theorem name              | Lean theorem name            | proven | Category              |
|------------------------------|------------------------------|--------|-----------------------|
| open_rec_lc_core             | open_rec_lc_core             | no     | substitution/open     |
| open_rec_lc                  | open_rec_lc                  | no     | substitution/open     |
| open_t_var_type              | open_t_var_type              | no     | substitution/open     |
| subst_fresh                  | subst_fresh                  | no     | substitution          |
| subst_open_rec               | subst_open_rec               | no     | substitution          |
| subst_t_open_t               | substT_openT                 | no     | substitution          |
| subst_e_open_e               | substE_openE                 | no     | substitution          |
| subst_t_open_t_var           | substT_openT_var             | no     | substitution          |
| subst_e_open_e_var           | substE_openE_var             | no     | substitution          |
| subst_t_intro                | substT_intro                 | no     | substitution          |
| subst_e_intro                | substE_intro                 | no     | substitution          |
| subst_lc                     | subst_lc                     | no     | regularity            |
| subst_t_type                 | substT_type                  | no     | regularity            |
| subst_e_term                 | substE_term                  | no     | regularity            |
| subst_e_value                | substE_value                 | no     | regularity            |
| value_is_term                | value_is_term                | no     | regularity            |
| wf_lc                        | wf_lc                        | no     | regularity            |
| wft_type                     | wft_type                     | no     | regularity            |
| wfe_term                     | wfe_term                     | no     | regularity            |
| wf_weaken                    | wf_weaken                    | no     | weakening             |
| wft_weaken                   | wft_weaken                   | no     | weakening             |
| wft_weaken_empty             | wft_weaken_empty             | no     | weakening             |
| wfe_weaken                   | wfe_weaken                   | no     | weakening             |
| wfe_weaken_empty             | wfe_weaken_empty             | no     | weakening             |
| wf_narrow                    | wf_narrow                    | no     | narrowing             |
| wft_narrow                   | wft_narrow                   | no     | narrowing             |
| wf_subst                     | wf_subst                     | no     | substitution          |
| wft_subst                    | wft_subst                    | no     | substitution          |
| wft_subst1                   | wft_subst1                   | no     | substitution          |
| wft_subst_empty              | wft_subst_empty              | no     | substitution          |
| wft_open                     | wft_open                     | no     | opening               |
| ok_from_okt                  | ok_from_okt                  | no     | environment           |
| wft_from_env_has             | wft_from_env_has             | no     | environment           |
| wft_from_okt                 | wft_from_okt                 | no     | environment           |
| wft_weaken_right             | wft_weaken_right             | no     | weakening             |
| okt_push_inv                 | okt_push_inv                 | no     | environment           |
| okt_push_type                | okt_push_type                | no     | environment           |
| okt_narrow                   | okt_narrow                   | no     | environment           |
| okt_subst                    | okt_subst                    | no     | environment           |
| okt_subst1                   | okt_subst1                   | no     | environment           |
| notin_fv_open_rec            | notin_fv_open_rec            | no     | fv                    |
| notin_fv_t_open              | notin_fv_t_open              | no     | fv                    |
| notin_fv_e_open              | notin_fv_e_open              | no     | fv                    |
| notin_fv_wf_rec              | notin_fv_wf_rec              | no     | fv                    |
| notin_fv_wf                  | notin_fv_wf                  | no     | fv                    |
| map_subst_id                 | map_subst_id                 | no     | substitution/env      |
| sub_has_regular              | sub_has_regular              | no     | regularity            |
| sub_regular                  | sub_regular                  | no     | regularity            |
| has_regular                  | has_regular                  | no     | regularity            |
| has_regular_e                | has_regular_e                | no     | regularity            |
| typing_regular               | typing_regular               | no     | regularity            |
| value_regular                | value_regular                | no     | regularity            |
| red_regular                  | red_regular                  | no     | regularity            |
| sub_reflexivity              | sub_reflexivity              | no     | subtyping             |
| sub_has_weakening            | sub_has_weakening            | no     | weakening             |
| sub_weakening                | sub_weakening                | no     | weakening             |
| sub_weakening1               | sub_weakening1               | no     | weakening             |
| sub_weakening_empty          | sub_weakening_empty          | no     | weakening             |
| has_weakening                | has_weakening                | no     | weakening             |
| has_weakening1               | has_weakening1               | no     | weakening             |
| has_weakening_empty          | has_weakening_empty          | no     | weakening             |
| sub_has_narrowing_aux        | sub_has_narrowing_aux        | no     | narrowing             |
| sub_narrowing                | sub_narrowing                | no     | narrowing             |
| sub_narrowing_empty          | sub_narrowing_empty          | no     | narrowing             |
| has_value_var                | has_value_var                | no     | regularity            |
| var_typing_has               | var_typing_has               | no     | typing                |
| val_typing_has               | val_typing_has               | no     | typing                |
| sub_has_through_subst        | sub_has_through_subst        | no     | substitution          |
| typing_weakening             | typing_weakening             | no     | weakening             |
| typing_narrowing             | typing_narrowing             | no     | narrowing             |
| typing_narrowing_empty       | typing_narrowing_empty       | no     | narrowing             |
| typing_through_subst         | typing_through_subst         | no     | substitution          |
| psub_sub                     | psub_sub                     | no     | subtyping             |
| has_empty_value              | has_empty_value              | no     | regularity            |
| possible_types_value         | possible_types_value         | no     | canonical forms       |
| possible_types_wfe           | possible_types_wfe           | no     | canonical forms       |
| possible_types_wft           | possible_types_wft           | no     | canonical forms       |
| has_empty_var_false          | has_empty_var_false          | no     | regularity            |
| possible_types_closure_psub  | possible_types_closure_psub  | no     | canonical forms       |
| psub_reflexivity             | psub_reflexivity             | no     | subtyping             |
| sub_psub_aux                 | sub_psub_aux                 | no     | subtyping             |
| sub_psub                     | sub_psub                     | no     | subtyping             |
| possible_types_closure       | possible_types_closure       | no     | canonical forms       |
| possible_types_typing        | possible_types_typing        | no     | canonical forms       |
| typing_inv_abs               | typing_inv_abs               | no     | inversion             |
| canonical_form_abs           | canonical_form_abs           | no     | canonical forms       |
| canonical_form_mem           | canonical_form_mem           | no     | canonical forms       |
| typing_through_subst1        | typing_through_subst1        | no     | substitution          |
| value_red_contra             | value_red_contra             | no     | preservation helper   |
| preservation_result          | preservation_result          | no     | meta-property         |
| progress_result              | progress_result              | no     | meta-property         |

TODO
- Synchronize Lean theorem signatures with the current minimal skeleton (many require introducing additional defs in Def.lean).
- Maintain declaration order and expand the scaffold with sorry stubs incrementally.
