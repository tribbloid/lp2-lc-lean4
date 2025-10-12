# Def.progress.md — Dot_top_bot

List of Coq definitions/types/inductives and their Lean counterparts in `Lp2lc/Active/Dot_top_bot/Def.lean`.

Columns:
- Coq name
- Lean name
- Category

| Coq name | Lean name | Category |
|---|---|---|
| typ_label (Parameter) | `typ_label` (structure) | Syntax |
| trm_label (Parameter) | `trm_label` (structure) | Syntax |
| label | `label` | Syntax |
| avar | `avar` | Syntax |
| typ | `typ` | Syntax |
| dec | `dec` | Syntax |
| trm | `trm` | Syntax |
| val | `val` | Syntax |
| def (renamed) | `defn` | Syntax |
| defs | `defs` | Syntax |
| ctx := env typ | `ctx := List (Var × typ)` | Environments |
| sto := env val | `sto := List (Var × val)` | Environments |
| label_of_def | `label_of_def` | Records |
| label_of_dec | `label_of_dec` | Records |
| get_def | `get_def` | Records |
| defs_has | `defs_has` | Records |
| defs_hasnt | `defs_hasnt` | Records |
| open_rec_avar | `open_rec_avar` | Opening |
| open_rec_typ/dec/trm/val/def/defs | `open_rec_typ/…` (mutual) | Opening |
| open_avar/typ/dec/trm/val/def/defs | `open_…` abbreviations | Opening |
| fv_avar | `fv_avar` | Free variables |
| fv_typ/dec/trm/val/def/defs | `fv_typ/…` (mutual) | Free variables |
| fv_ctx_types | `fv_ctx_types` | Free variables |
| red | `red` | Operational semantics |
| tymode | `tymode` | Typing |
| submode | `submode` | Typing |
| ty_trm | `ty_trm` | Typing |
| ty_def | `ty_def` | Typing |
| ty_defs | `ty_defs` | Typing |
| subtyp | `subtyp` (with top/bot rules) | Subtyping |
| wf_sto | `wf_sto` | Store well-formedness |
| record_dec | `record_dec` | Records |
| record_typ | `record_typ` | Records |
| record_type | `record_type` | Records |
| record_sub | `record_sub` | Records |
| has_member | `has_member` | Member queries |
| has_member_rules | `has_member_rules` | Member queries |
| possible_types | `possible_types` | Possible types |
| record_has | `record_has` | Records |
| normal_form | `normal_form` | Normal forms |
| subenv | `subenv` (in Auxiliary.lean) | Environment relations |

Notes:
- `def` in Coq is renamed to `defn` in Lean to avoid keyword conflict; all uses updated consistently.
- Environment helpers `Env.binds`/`Env.dom` specialized locally; shared `Var`/`Vars`/`ok` come from `Lp2lc/Active/Shared.lean`.
