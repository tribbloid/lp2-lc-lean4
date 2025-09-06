## Coq to Lean Conversion Notes

This document summarizes the conversion decisions and mappings made during the translation of the Coq proofs in `Lp2lc_coq/Active` to Lean 4.

### General Approach

The conversion process followed the workflow defined in `prompts/Define.md`. The core tasks for each file were:

1.  **File Structure Setup:** A corresponding directory and `Def.lean` file were created in `src/Lp2lc/Active` for each Coq file.
2.  **Definition Conversion:** All definitions, axioms, and types were extracted from the Coq source and converted to Lean 4 syntax in the corresponding `Def.lean` file.
3.  **Proof Scaffolding:** All theorems and lemmas were extracted and scaffolded with `sorry` in the central `src/Lp2lc/Active/Fsub.lean` file, as per the user's rules.

### Coq to Lean Mappings

*   **`Inductive` to `inductive`:** Standard mapping.
*   **`Record` to `structure`:** Standard mapping.
*   **`Definition` to `def`:** Standard mapping.
*   **`Fixpoint` to `def`:** The `decreasing_by` tactic was not needed as the recursion was structurally obvious in all cases.
*   **`Lemma` and `Theorem` to `theorem`:** All Coq `Lemma` and `Theorem` declarations were converted to Lean `theorem` declarations.
*   **`Set` and `Prop` to `Prop` or `Type`:** Coq's `Set` and `Prop` were generally mapped to Lean's `Prop`. `Type` was used when the type was not a proposition.
*   **`var` from `LibLN` to a Lean `structure`:** As per the conversion rules, the `var` type was converted to a Lean `structure` with a `String` field.
*   **`env` from `LibEnv` to `List (String × bind)`:** The `env` type was mapped to a list of pairs, representing an association list.
*   **`Require Import` to `import`:** Coq's `Require Import` statements were mapped to Lean's `import` statements. The `TLC` libraries (`LibTactics`, `LibLN`, etc.) were determined to be part of the project's own codebase and their functionality was either converted directly or assumed to be available from `Mathlib`.

### Notations

No custom notations were required for this conversion.

