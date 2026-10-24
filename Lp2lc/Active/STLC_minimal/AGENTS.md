# AGENTS.md - STLC_minimal

## Machine-generated module

Every Lean file in this directory is machine-generated. Do **NOT** edit them by hand: change
[the generator](../../../.agent/script/gen_stlc_minimal.sh) and regenerate instead.

## Replaying the generation

From the repository root:

```sh
sh .agent/script/gen_stlc_minimal.sh
lake build Lp2lc.Active.STLC_minimal.mod
```

The generator copies the minimal dependency closure of `Serial/__Eval_certifiedByInfer.lean`
(`STLCDef.lean`, `Serial/Def.lean`, `Serial/Infra.lean`, `Serial/Infer.lean`, and the proof) from
`Lp2lc/Active/STLC` at revision `226bedc617f1cd77f934dd60c4b6652cd940f4dc`, renames the
`Lp2lc.Active.STLC` namespace to `Lp2lc.Active.STLC_minimal`, repairs the stale `Serial.__Infer` import, restores
the `fnPrimitive` cases that the proof lacks, and writes the proof as `Serial/Eval_certifiedByInfer.lean`.
