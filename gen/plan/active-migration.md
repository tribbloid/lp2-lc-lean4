# Active migration plan (Coq → Lean 4)

Status snapshot
- Existing Lean modules: Ddia, Fsub (with Def/Auxiliary/Proof and progress/spec files).
- To scaffold next: Dsub, Dsubsup, FsubL_alt.

Plan
1) Create module structure for Dsub, Dsubsup, FsubL_alt under Lp2lc/Active/<Name> with 6 files per FileStructure.md.
2) Implement Definition Conversion for Dsub first (full AST, opening, lc, env, wft/wfe/okt, sub/has, typing, red, fv/subst).
3) Add Proof scaffolding (statements with sorry) incrementally, starting from theorems with smallest line numbers.
4) Build after each edit using lake build.
5) Update Def.progress.md and Proof.progress.md continuously.
6) Document decisions in specs.md.

Order (ascending size among remaining)
- FsubL_alt (1,713) → Dsub (1,774) → Dsubsup (1,800).

Build+verify checklist
- [ ] Dsub: Def.lean compiles
- [ ] Dsub: Proof.lean compiles with sorries
- [ ] Dsub: progress/specs updated
- [ ] FsubL_alt: structure scaffolding compiles
- [ ] Dsubsup: structure scaffolding compiles
- [ ] lake build green after all scaffolding

Notes
- All proofs remain sorry at this stage; no proof discharge is attempted.
- Names and declaration order mirror Coq to ease later proof porting.
