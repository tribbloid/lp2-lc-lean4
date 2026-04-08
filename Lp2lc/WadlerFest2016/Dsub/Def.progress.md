# Dsub Def.progress.md

This file tracks the conversion of Coq declarations in Lp2lc_coq/Active/Dsub.v into Lean.

| Coq name | Lean name | Category |
|---|---|---|
| Inductive typ | typ | inductive |
| Inductive trm | trm | inductive |
| Fixpoint open_t_rec | open_t_rec | function |
| Fixpoint open_e_rec | open_e_rec | function |
| Definition open_t | open_t | definition |
| Definition open_e | open_e | definition |
| Notation t open_t_var x | T open_t_var X | notation |
| Notation t open_e_var x | t open_e_var x | notation |
| Inductive type | def_type | inductive (renamed) |
| Inductive term | def_term | inductive (renamed) |
| Inductive value | value | inductive |
| Definition env | env | alias |
| Inductive wft | wft | inductive |
| Inductive wfe | wfe | inductive |
| Inductive okt | okt | inductive |
| Inductive sub | sub | inductive |
| Inductive has | has | inductive |
| Inductive typing | typing | inductive |
| Inductive red | red | inductive |
| Definition preservation | preservation | definition |
| Definition progress | progress | definition |
| Fixpoint fv_t | fv_t | function |
| Fixpoint fv_e | fv_e | function |
| Fixpoint subst_t | subst_t | function |
| Fixpoint subst_e | subst_e | function |
| Inductive psub | psub | inductive |
| Inductive possible_types | possible_types | inductive |
