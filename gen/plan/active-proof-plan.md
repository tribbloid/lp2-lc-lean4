# Active proof plan

Scope
- Centralize proof effort later, but for now we scaffold theorem statements in each module’s Proof.lean with `sorry`.
- When proving later, prioritize:
  1) theorems first (as tagged in the Coq sources),
  2) then lemmas, with smaller line numbers first.

Granularity and location
- Keep theorem statements in the module namespaces (Proof.lean) to align with FileStructure.md.
- Use Auxiliary.lean for minimal axioms (e.g., ok : env → Prop) and Aesop hints.

Tracking
- Mark each theorem in Proof.progress.md with Proven? = no, until proofs are completed.
- Update progress files after each change.

Next batch candidates (after full scaffolding)
- Dsub: opening/substitution facts (earliest lemmas), weakening/narrowing, typing substitution.
- FsubL_alt, Dsubsup: mirror the same early lemma families.
