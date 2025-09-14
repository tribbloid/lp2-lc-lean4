# Structure audit (initial)

- Module mapping:
  - Ddia.v → Lp2lc/Active/Ddia/ (present)
  - Dsub.v → Lp2lc/Active/Dsub/ (present)
  - Dsubsup.v → Lp2lc/Active/Dsubsup/ (present)
  - Fsub.v → Lp2lc/Active/Fsub/ (present)
  - FsubL_alt.v → Lp2lc/Active/FsubL_alt/ (present)
- Required files per CodeStructure:
  - Def.lean, Proof.lean, Auxiliary.lean, Def.progress.md, Proof.progress.md, question.md
- Current gaps:
  - question.md missing in all modules.
- Shared items:
  - Shared.lean exists and defines Var/Vars and Env helpers, plus var_fresh axiom.
  - ok is repeatedly declared in several modules (Ddia/Auxiliary.lean, Dsub/Auxiliary.lean, Dsubsup/Auxiliary.lean) and Fsub/Def.lean contains an `axiom ok`.

Plan:
- Centralize `ok` in Shared.lean with a polymorphic signature over env types to avoid duplication.
- Remove per-module `axiom ok` declarations.
- Add question.md to each module.
