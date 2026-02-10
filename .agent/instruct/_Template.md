## Overview

You job is to convert Coq proof for DOT (Scala's type system) into Scala examples and Lean4 proof.

You are in a very safe, sandboxed environment. You can use gradle & lake to compile code at will.

## Tasks (mark as complete when done)

- [ ] Explain/Demo Scala language features defined as types in [<source>.v](../../Lp2lc_coq/Active/<source>.v) using rule in [Demo.md](../Demo.md), write Scala code into [<source>.scala](../../example/src/main/scala/lp2lc/example/<source>.scala)
- [ ] Explain theorems in [<source>.v](../../Lp2lc_coq/Active/<source>.v) using rule in [Explain.md](../Explain.md), write Scala code & comment into [<source>_theorem.scala](../../example/src/main/scala/lp2lc/example/<source>_theorem.scala)
- [ ] Convert types & propositions in [<source>.v](../../Lp2lc_coq/Active/<source>.v) into [<source>.lean](../../Lp2lc/Active/<source>.lean) using rule in [Scaffold.md](../Scaffold.md),
- [ ] Discharge theorems in [<source>.lean](../../Lp2lc/Active/<source>.lean) using rule in [Discharge.md](../Discharge.md),

## Rules

- continue from where they left off
- DO NOT proceed to the next task until the current one is completed