# Objective: Upgrade Coq Proof Files

Could you upgrade the syntax of the Coq file(s) from 8.4 to 8.18? Do not touch other files

# Rules

- LibLN and some other libraries are moved to TLC library, when importing them, the TLC prefix will be required.
  - e.g. `Require Import LibLN.` should be replaced with `Require Import TLC.LibLN.`.
- All Hint defined in the code should be add into `core` hint database.
- Do NOT use `admit` or `give_up`.
- Code that compiles successfully without error or warning should be preserved.
- Only attempt to upgrade a proof using the following recommendations if it produced error or warning:
  - TLC tactic named `xxx*` should be replaced with `exxx`, where xxx is the name of the tactic:
    - for example. `auto*` tactic with no argument should be replaced with `eauto`.
  - in the above case, if the TLC tactic is applied on parameter(s), an extra `using` keyword may be required before the parameter(s):
    - e.g. `auto* X` should be replaced with `eauto using X`
  - `Omega` library has been superseded by `Lia`, so `Require Import Omega.` should be replaced with `Require Import Lia.`.
- Do NOT delete code, every line in the original proof is necessary.
<!-- - Your proofs should not be much longer than the old version, if you can't make the proof short enough, you should insert an `admit` where proof check fails (but do not delete other part of the proof), and move to the next one. -->
- Your proofs should not be much longer than the original version. If you can't make the proof short enough, you should introduce a minimal and temporary axiom and use it as a placeholder to replace the missing step of the proof, do NOT delete or replace other parts or steps of the proof. Afterwards, move on to the remainder of the file.

# Workflow

1. Scan the entire `active` directory, find all the Coq files and rank them by length.
2. For each file, the upgrade should be from top-down, compile often (using installed coqc) to verify each revision.
3. When upgrading multiple coq files, you should apply upgrade sequentially and from the shortest file to longer ones.
4. apply upgrade to many files as possible.

Do not use make file to compile the whole directory.
