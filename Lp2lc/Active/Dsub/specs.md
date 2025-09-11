# Specs: Dsub (Active)

- Env model: List (Var × typ); LibEnv-like helpers via Shared.lean.
- ok : env → Prop is kept abstract in Auxiliary.lean.
- Keep declarations aligned with Coq names and order; ASTs live in Type.
- Subtyping for typ_mem distinguishes lower (true) vs upper (false) bounds per Coq.
- Proofs remain sorry; fill them later following theorems-first, smaller-lines-first policy.
