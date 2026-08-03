# STLC TODO

## Main Problem

The same AST definition is used in 3 different Ctx: Compiling/Eval/Proving.

- if they use the same UID, then one UID can be from Ctx and be used in another, which makes the proof vacuous
- if they use different UID, their AST will be different, and requires conversion before being used to define Adequacy conjecture

### Fix 1

- improve AST: Trm.ref to Ctx requires both the UID and evidence/receipt
- this only affects Trm.ref, not Val.fn (evidence are erased by proof irrelevance and can't affect AST). So the entire AST is covariant to UID type, which is an advantage.
- such covariance allow the same Adequacy conjecture to be used, the AST of UID-with-evidence can be only an intermediate artefact for proving

### Fix 2

- same AST, but compilation_proof takes Trm of UID and produce AST of UID-with-evidence



## How to fix the vacuous proof

