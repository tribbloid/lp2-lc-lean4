# Module report: FsubL_alt

Status:
- Coq: Lp2lc_coq/Active/FsubL_alt.v (1713 lines)
- Lean module: Lp2lc/Active/FsubL_alt

Findings:
- Auxiliary.lean had duplicate ok; switched to shared ok.
- Proof.lean currently contains many axioms placeholders; need to replace with theorem stubs or track in Proof.progress.md.

Next:
- Remove axioms from Proof.lean and create properly typed stubs with sorry.
- Add question.md.
