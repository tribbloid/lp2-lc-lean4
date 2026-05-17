# Scaffold Steps

## Understand File Structure

- Read the coq file and corresponding lean file structure as defined [here](CodeStructure.md).
- Understand all theorems and their relationship.

## Discharge Theorems

- Discharge each unimplemented theorem by implementing its proof top-down approach.
- Replace `sorry` with complete proofs, use the original Coq proof as a reference.
- Add auxiliary tactics/lemmas to `Auxiliary.lean` as needed as defined [here](ConversionRules.md); do not add more
  theorem to `Proof.lean`.
- Do not delete or modify proofs that are already successfully verified.
- Build and verify after every iteration.
- Update `Proof.progress.md` to reflect the latest progress
- If progress has been made, git commit into the current branch.
- Doublecheck that:
    -[ ] Each lean theorem is fully implemented/discharged.
    -[ ] The project builds successfully.
