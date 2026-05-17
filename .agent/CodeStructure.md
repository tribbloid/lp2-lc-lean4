### Code Structure

- All Lean files and modules should be under [this](../Lp2lc/Active) module
- The directory always contains 5 files:
    1. `Def.lean`: definitions, types.
    2. `Proof.lean`: original theorems and proofs.
    3. `Auxiliary.lean`: auxiliary tactics and lemmas to support the original theorems.
    6. `Glossary.md`: contains a list of all lemma and theorems, each annotated with a short
       explanation about their purpose.
- The directory also contains a subdirectory `notes` which contains memorandum that summarises requirements and
  specifications of the proof, every question you asked and their answeres should be recorded in this directory.
- Each directory/module (including their parents `Lp2lc` and `Lp2lc/Active`) should be accompanied by a module
  aggregator lean file with imports
- Code shared between modules should be in `/Lp2lc/Active`.
- DO NOT write into any other files.
