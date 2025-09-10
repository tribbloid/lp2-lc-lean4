# Specs: Fsub (Active)

- Shared imports: Lp2lc/Shared.lean (Var, Vars, Env.* helpers)
- Env model: List (Var × bind) as in Fsub.Def.lean
- ok : env → Prop exists as an axiom in Def.lean (keep as is for now)
- Hints: add @[aesop] selectively for constructor-like lemmas later
- Proofs: to be centralized in Lp2lc/Active/Fsub.lean when implementing (current phase = scaffolding)
