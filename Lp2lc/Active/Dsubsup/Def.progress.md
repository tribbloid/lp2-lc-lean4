# Dsubsup (D<:>) — Def.progress

This file tracks definitions, inductives, and operations mirrored from Coq
`Lp2lc_coq/Active/Dsubsup.v` into `Lp2lc/Active/Dsubsup/Def.lean`.

Conventions
- Coq names are preserved when possible. Lean uses `Trm`, `Typ`, `openT`, `openE`, `fvT`, `fvE`, `substT`, `substE`, etc.
- Environments are `Env := List (Var × Typ)` with `Okt` for well-formedness.

Coverage Table (initial scaffold; counts approximate by manual scan)

| Coq name            | Lean name        | Category            |
|---------------------|------------------|---------------------|
| typ                 | Typ              | inductive           |
| trm                 | Trm              | inductive           |
| open_t_rec/open_e_rec| openTRec/openERec | operation         |
| open_t/open_e       | openT/openE      | operation           |
| type/term           | LcT/LcE          | predicate (lc)      |
| value               | Value            | predicate           |
| env, wft, wfe       | Env, Wft, Wfe    | env + wf predicates |
| okt                 | Okt              | env well-formedness |
| sub / has           | Sub / Has        | relations           |
| typing              | Typing           | relation            |
| red                 | Red              | relation            |
| fv_t/fv_e           | fvT/fvE          | operation           |
| subst_t/subst_e     | substT/substE    | operation           |

Notes
- We intentionally keep the skeleton minimal, enough to typecheck theorem statements.
- LibLN-specific lemmas are not replicated here.
- Any missing constructs identified later will be added incrementally.