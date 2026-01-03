import «Lp2lc».Active.Dsubsup.Def
import «Lp2lc».Active.Dsubsup.Auxiliary
import «Lp2lc».Active.Dsubsup.Proof

/-!
# Dsubsup (D<:>) — Aggregator

Coq source: `Lp2lc_coq/Active/Dsubsup.v`

This module aggregates the ported Lean submodules for Dsubsup:
- `Def`: core syntax, judgments, and operations (no theorems)
- `Auxiliary`: auxiliary lemmas/tactics (no axioms allowed)
- `Proof`: theorem statements scaffolded with `sorry` proofs

Notes
- Only `Lp2lc.Active.Shared` is used as a shared dependency.
- Do not import other `Active` submodules here to keep modules independent.
- Successful proofs may later be migrated to the project’s preferred location per user rule, but statement ownership remains here.
- All theorem statements are maintained in declaration order relative to the Coq source.
- See `.agents/CodeStructure.md` and `.agents/ConversionRules.md` for conventions.
- See `Lp2lc/Active/Dsubsup/Proof.progress.md` and `.../Def.progress.md` for coverage.
-/
