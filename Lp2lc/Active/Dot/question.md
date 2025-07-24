- Module: Dot
- Source: Lp2lc_coq/Active/Dot.v
- Scope: questions and decisions for conversion

1) Proof placement vs personal rule
- Personal rule indicates moving successful proofs into Lp2lc/Active/Fsub.lean. Project CodeStructure.md requires per-module Proof.lean. I will keep Dot proofs in Lp2lc/Active/Dot/Proof.lean to respect per-module independence. Please confirm if you want a cross-module aggregator for finalized proofs.

2) Naming: Coq `def` vs Lean `def`
- Coq uses an inductive named `def` for definitions inside a record’s defs list. Lean reserves `def` for definitions. I renamed that inductive to `defn`. All uses are consistently updated. If you prefer a different name (e.g., dfn or ddef), please advise.

3) Label types
- Coq has parameters `typ_label`, `trm_label`. I introduced simple structures with a `String` field and derived instances (DecidableEq, BEq, Hashable, Repr). If you prefer opaque types with axioms or a custom enumeration, please specify.

4) Environments
- Coq uses LibEnv `env`. Shared.lean provides an abstract `ok` and general helpers. For Dot, I specialize environments as `List (Var × typ)` and `List (Var × val)` and defined minimal `Env.binds` and `Env.dom`. If you have a common environment abstraction to reuse, I can refactor to it.

5) Free-variable and opening operations
- Implemented mutually recursive functions mirroring Coq definitions with Finset Vars. Edge cases and tactics to be refined as we progress.

6) possible_types completeness
- I scaffolded a subset of constructors; remaining constructors from the Coq definition will be added as we enumerate all declarations and theorems.

7) Aesop hints
- Added constructor-level aesop hints to mirror Coq Hint Constructors. If this is too aggressive, I can narrow them.

8) Line number comments
- I annotated key blocks with approximate Coq line numbers from the file we read. After extraction indexing, I’ll refine to exact lines for each declaration.
