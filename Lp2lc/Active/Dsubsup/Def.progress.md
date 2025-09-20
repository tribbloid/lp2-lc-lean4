# Dsubsup (D<:>) — Def.progress

This file tracks definitions, inductives, and operations mirrored from Coq
`Lp2lc_coq/Active/Dsubsup.v` into `Lp2lc/Active/Dsubsup/Def.lean`.

Conventions
- Coq names are preserved when possible. Lean uses `Trm`, `Typ`, `openTRec/openERec`, `openT/openE`, `fvT/fvE`, `substT/substE`, etc.
- Environments are `Env := List (Var × Typ)` with `Okt` for well-formedness.
- `ok : Env → Prop` is provided abstractly by `Lp2lc.Active.Shared`.

Coverage Table (scaffold)

| Coq name                | Lean name           | Category                 |
|-------------------------|---------------------|--------------------------|
| typ                     | Typ                 | inductive                |
| trm                     | Trm                 | inductive                |
| open_t_rec/open_e_rec   | openTRec/openERec   | operation (opening)      |
| open_t/open_e           | openT/openE         | operation (opening)      |
| type/term               | LcT/LcE             | predicate (local closure)|
| value                   | Value               | predicate                |
| env, wft, wfe           | Env, Wft, Wfe       | env + wf predicates      |
| okt                     | Okt                 | env well-formedness      |
| sub / has               | Sub / Has           | relations                |
| typing                  | Typing              | relation                 |
| red                     | Red                 | relation                 |
| fv_t/fv_e               | fvT/fvE             | operation                |
| subst_t/subst_e         | substT/substE       | operation                |
| map (subst) on env      | mapSubst            | env operation            |
| psub                    | PSub                | inductive (proof infra)  |
| possible_types          | PossibleTypes       | inductive (proof infra)  |

Notes
- Locally nameless operations are implemented (mutual recursions) to allow expressing statements; proofs live in `Proof.lean`.
- `Wft`, `Wfe`, `Sub`, `Has` remain abstract (axioms) to keep this file definitional-only.
- Additions will be made incrementally if new Coq constructs are needed.
