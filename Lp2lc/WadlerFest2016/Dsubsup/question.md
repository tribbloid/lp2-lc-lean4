# Dsubsup (D<:>) — question.md

Purpose
- Capture design choices and open issues while scaffolding the Dsubsup conversion from Coq.

Decisions
- Axiomatized predicates: Wft, Wfe, Sub, Has remain abstract constants in Def.lean to keep the file purely definitional. This matches the instructions to avoid proofs/lemmas in Def and allows Proof.lean to state all lemmas with sorry.
- Locally nameless operations (openTRec/openERec, openT/openE, fvT/fvE, substT/substE) are implemented to enable faithful statement signatures mirroring Coq.
- Added mapSubst to map substitutions over environments, used by typing_through_subst and related lemmas in Proof.lean.
- Introduced PSub and PossibleTypes inductives as scaffolds since several canonical-form and preservation lemmas in Coq rely on them.

Open issues
- If we later port Wft/Wfe/Sub/Has into mutually inductive definitions (like the Dsub module does), we must:
  - Update their use sites in Proof.lean, possibly replacing some axioms with constructors.
  - Revise some lemma statements to reference the inductive forms.
- fvT/fvE currently mirror Coq shapes; if additional term/type constructors are added, we must extend fv and subst accordingly.
- Tactics (gather_vars, apply_fresh) are not reproduced; statements assume we can phrase results without them.

Next steps (optional)
- Port Wft/Wfe/Sub/Has to inductives for stronger regularity lemmas and more faithful proofs.
- Start discharging simplest lemmas (e.g., trivial regularity wrappers) and, per the user’s rule, migrate completed proofs to the main file Lp2lc/Active/Fsub.lean while keeping statement ownership here.
