
The directory `active` contains some coq proof files written in coq 8.4. Could you upgrade their syntax to be compatible with coq 8.18? Do not touch other directories.

The structure of the project is written in `./AGENT.md`

Here are the rules:

- LibLN and some other libraries are moved to TLC library, when importing them, the TLC prefix will be required.
  - e.g. `Require Import LibLN.` should be replaced with `Require Import TLC.LibLN.`.
- a tactic named `xxx*` should be replaced with `exxx`, where xxx is the name of the tactic:
  - for example. `auto*` tactic with no argument should be replaced with `eauto`.
- in the above case, if the tactic is applied on parameter(s), an extra `using` keyword may be required before the parameter(s):
  - e.g. `auto* X` should be replaced with `eauto using X`
- `Omega` library has been superseded by `Lia`, so `Require Import Omega.` should be replaced with `Require Import Lia.`.
- All Hint defined in the code should be add into `core` hint database.
- DO NOT delete code, every line in the original proof is necessary.
- Your proofs should not be much longer than the old version, if you can't make the proof short enough, you should insert an `admit` where proof check fails (but do not delete other part of the proof), and move to the next one.
- start your upgrade from `Fsub.v`, then upgrade and compile other coq files individually, starting from the shortest and gradually proceed to longer ones. Do not use make file to compile the whole directory.

try to upgrade as many files as possible

Coq 8.18 with compatible TLC are already installed, compile often to verify your revision.
