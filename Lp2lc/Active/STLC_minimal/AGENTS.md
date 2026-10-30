# AGENTS.md - STLC_minimal

## Machine-generated module

Every Lean file in this directory is machine-generated. Do **NOT** edit them by hand: update the STLC sources or
[the generator](../../../.agent/script/gen_stlc_minimal.sh), then regenerate.

## Replaying the generation

From the repository root:

```sh
sh .agent/script/gen_stlc_minimal.sh
lake build Lp2lc.Active.STLC_minimal.mod Tests.STLC_minimal.mod
```

The generator removes previous generated Lean files, then copies the STLC dependency closure of serial inference,
certified evaluation, their test suites, and the value, type, and term demos. Production modules live here; migrated
tests and demos live in `Tests/STLC_minimal`. Both directories have generated `mod.lean` aggregators.

All Lean comments are stripped, including nested block comments; string literals are preserved. Module references and
namespaces are renamed from `STLC` to `STLC_minimal`. Update the sources or generator and regenerate both trees together.
