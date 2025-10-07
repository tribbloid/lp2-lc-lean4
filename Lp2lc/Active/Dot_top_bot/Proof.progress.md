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

Notes:
- Maintain original order as in Coq where possible; this table currently covers the subset scaffolded in `Proof.lean`. More entries will be appended as scaffolding proceeds across the file.
