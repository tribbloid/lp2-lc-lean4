# Def.progress (Ddia)

Coq file: Lp2lc_coq/Active/Ddia.v
This table maps Coq declarations (non-theorems) to Lean counterparts in Def.lean.

| Coq name            | Lean name        | Category        |
|---------------------|------------------|-----------------|
| typ                 | typ              | inductive       |
| trm                 | trm              | inductive       |
| open_t_rec          | open_t_rec       | def             |
| open_e_rec          | open_e_rec       | def             |
| open_t              | open_t           | def             |
| open_e              | open_e           | def             |
| type (local closure)| def_type         | inductive       |
| term (local closure)| def_term         | inductive       |
| value               | value            | inductive       |
| env                 | env              | alias           |
| dom                 | dom              | helper          |
| binds               | binds            | helper          |
| wft                 | wft              | inductive       |
| wfe                 | wfe              | inductive       |
| okt                 | okt              | inductive       |
| sub                 | sub              | inductive       |
| has                 | has              | inductive       |
| typing              | typing           | inductive       |
| red                 | red              | inductive       |
| preservation        | preservation     | Prop alias      |
| progress            | progress         | Prop alias      |
| fv_t                | fv_t             | def             |
| fv_e                | fv_e             | def             |
| subst_t             | subst_t          | def             |
| subst_e             | subst_e          | def             |
| map (subst over env)| map_subst_t      | def/helper      |

Notes:
- Ordering follows the Coq source where applicable; each Lean definition is prefixed by a Coq line-range comment in Def.lean.
- No theorems appear in Def.lean per CodeStructure.md.
