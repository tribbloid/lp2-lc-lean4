# AGENTS.md - STLC_minimal

## Machine-generated module

Every Lean file in this directory is machine-generated. Do **NOT** edit them by hand: update the STLC sources or
[the generator](../../../../.agent/script/gen_stlc_minimal.sh), then regenerate.

## Replaying the generation

From the repository root:

```sh
sh .agent/script/gen_stlc_minimal.sh
lake build Lp2lc.Active.STLC_minimal.mod
```

The generator copies the minimal dependency closure of `Serial/__Eval_certifiedByInfer.lean`
(`STLCDef.lean`, `Serial/Def.lean`, `Serial/Infra.lean`, `Serial/Infer.lean`, and the certified evaluator)
from `Lp2lc/Active/STLC` and renames the `Lp2lc.Active.STLC` namespace to `Lp2lc.Active.STLC_minimal`.
The generated evaluator is `Serial/__Eval_certifiedByInfer.lean`.
