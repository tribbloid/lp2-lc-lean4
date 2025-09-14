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

TODO
- Expand table to include all lemmas from the Coq file as we scaffold them.
- Synchronize names more tightly with exact Coq identifiers and line numbers.
