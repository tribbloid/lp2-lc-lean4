# Dsubsup - Define conversion plan

- Coq file: Lp2lc_coq/Active/Dsubsup.v (approx 1800 lines)
- Lean module: Lp2lc/Active/Dsubsup/

Overview and scope
- Current Lean status
- TODOs and deltas
- Key declarations
  - psub: [Coq L1459] in Lp2lc_coq/Active/Dsubsup.v; port exactly (mutual placement if necessary). Add [Coq L1459] comment in Lean.
Steps and notes
- Definition audit → Proof scaffolding → Docs → Build → Commit.
- Keep Prop for relations; no cross-module imports; annotate [Coq L###].
- Verify psub is included in Def.progress.md and referenced by name 1:1.
