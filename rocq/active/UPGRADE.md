Upgrade Guide
----------------------------

The directory `active` contains some coq proof files written in coq 8.4. Could you upgrade their syntax to be compatible with coq 8.18? Do not touch other directories.

The structure of the project is written in `./AGENT.md`

Here are the rules:

- LibLN and some other libraries are moved to TLC library, when importing them, the TLC prefix will be required.
  - e.g. `Require Import LibLN.` should be replaced with `Require Import TLC.LibLN.`.
- `auto*` tactic with no argument should be replaced with `eauto`
- `auto*` tactic with 1 argument should be replaced with `eauto using`
- `Omega` library has been superseded by `Lia`, so `Require Import Omega.` should be replaced with `Require Import Lia.`.
- All Hint defined in the code should be add into `core` hint database.
- DO NOT delete code, every line in the original proof is necessary.
- Your code should not be much longer than the old version, this implies a diverging proving process and should be stopped.
- start your upgrade from `Fsub.v`, then upgrade and compile other coq files individually, starting from the shortest and gradually proceed to longer ones. Do not use make file to compile the whole directory.


Coq 8.18 with compatible TLC are already installed, compile often to verify your revision.
