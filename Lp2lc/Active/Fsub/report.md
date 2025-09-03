# Fsub Proof Implementation Progress Report

## Overview
This report tracks the progress of implementing proofs for the System-F with Subtyping formalization in Lean 4.

## Implementation Status

### Completed Proofs

#### 1. `wft_type` (Line 195)
**Description**: Proves that well-formed types in an environment are locally closed (satisfy `def_type`).
**Technique**: Structural induction on the well-formedness derivation.
**Key insight**: The proof follows directly from the structure of `wft` and `def_type` inductives.

#### 2. `okt_push_sub_type` (Line 288)
**Description**: Shows that if an environment extended with a subtyping binding is well-formed, then the bound type is locally closed.
**Technique**: Uses `okt_push_sub_inv` to extract the well-formedness condition, then applies `wft_type`.

#### 3. `okt_push_typ_type` (Line 302)
**Description**: Shows that if an environment extended with a typing binding is well-formed, then the bound type is locally closed.
**Technique**: Uses `okt_push_typ_inv` to extract the well-formedness condition, then applies `wft_type`.

#### 4. `okt_push_inv` (Line 271)
**Description**: Shows that if an environment with a binding is well-formed, the binding must be either a subtyping or typing binding.
**Technique**: Case analysis on the `okt` constructor.

#### 5. `okt_push_sub_inv` (Line 281)
**Description**: Inversion lemma for environments extended with subtyping bindings.
**Technique**: Direct case analysis on the `okt` constructor.

#### 6. `okt_push_typ_inv` (Line 295)
**Description**: Inversion lemma for environments extended with typing bindings.
**Technique**: Direct case analysis on the `okt` constructor.

#### 7. `value_regular` (Line 359)
**Description**: Shows that values are well-formed terms.
**Technique**: Case analysis on the value constructor, extracting the `def_term` hypothesis.

#### 8. `red_regular` (Line 367)
**Description**: Shows that reduction preserves term well-formedness.
**Technique**: Induction on the reduction relation, using `value_regular` for value cases.
**Note**: Two cases remain incomplete, requiring `subst_ee_term` and `subst_te_term` lemmas.

### Partially Completed Proofs

#### 1. `subst_tt_fresh` (Line 25)
**Description**: Substitution with a fresh variable leaves a type unchanged.
**Status**: Main structure complete, missing some case details.

#### 2. `subst_tt_open_tt` (Line 54)
**Description**: Commutation of substitution with opening.
**Status**: Uses `subst_tt_open_tt_rec` as the main lemma.

#### 3. `subst_tt_open_tt_var` (Line 62)
**Description**: Special case of substitution and opening with a variable.
**Status**: Structure complete using rewrites and case splits.

#### 4. `subst_tt_intro` (Line 72)
**Description**: Introduction rule for type substitution.
**Status**: Structure complete using previous lemmas.

#### 5. `ok_from_okt` (Line 237)
**Description**: Extract the `ok` predicate from `okt`.
**Status**: Structure complete but blocked by `ok` being an axiom.

### Remaining Work

The following categories of proofs remain to be implemented:

1. **Core substitution lemmas** (Lines 14-190): Foundation lemmas for substitution operations
2. **Well-formedness lemmas** (Lines 200-266): Properties of well-formed types and environments
3. **Environment lemmas** (Lines 309-344): Properties of environment operations
4. **Subtyping lemmas** (Lines 394-434): Properties of the subtyping relation
5. **Typing lemmas** (Lines 439-491): Properties of the typing relation
6. **Main theorems** (Lines 494-525): Preservation and progress theorems

## Next Steps

1. Complete the substitution lemmas that are blocking other proofs
2. Implement the remaining well-formedness properties
3. Work through the subtyping and typing lemmas
4. Finally tackle the preservation and progress theorems

## Statistics

- Total theorems: ~70
- Completed: 8
- Partially completed: 5
- Remaining: ~57
