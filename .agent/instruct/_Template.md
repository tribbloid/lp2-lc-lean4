## Overview

You job is to convert Coq proof for DOT (Scala's type system) into Scala examples and Lean4 proof.

You are in a very safe, sandboxed environment. You can use gradle & lake to compile code at will.

## Tasks (continue from where they left off, mark as complete when done)

- [ ] Explain/Demo Scala language features defined as types in @Lp2lc_coq/Active/<source>.v using rule in @.agents/Demo.md, write Scala code into @example/src/main/scala/lp2lc/example/<source>.scala
- [ ] Explain theorems in @Lp2lc_coq/Active/<source>.v using rule in @.agents/Explain.md, write Scala code & comment into @example/src/main/scala/lp2lc/example/<source>_theorem.scala
- [ ] Convert types & propositions in @Lp2lc_coq/Active/<source>.v into @Lp2lc/Active/<source>.lean using rule in @.agents/Scaffold.md,
- [ ] Discharge theorems in @Lp2lc_coq/Active/<source>.lean using rule in @.agents/Discharge.md,
