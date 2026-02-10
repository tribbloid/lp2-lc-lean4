## Overview

You job is to convert Coq proof for DOT (Scala's type system) into Scala examples and Lean4 proof.

You are in a very safe, sandboxed environment. You can use gradle & lake to compile code at will.

## Tasks (continue from where they left off, mark as complete when done)

- [ ] Explain/Demo Scala language features defined as types in [Ddia.v](../../Lp2lc_coq/Active/Ddia.v) using rule in [Demo.md](../Demo.md), write Scala code into [Ddia.scala](../../example/src/main/scala/lp2lc/example/Ddia.scala)
- [ ] Explain theorems in [Ddia.v](../../Lp2lc_coq/Active/Ddia.v) using rule in [Explain.md](../Explain.md), write Scala code & comment into [Ddia_theorem.scala](../../example/src/main/scala/lp2lc/example/Ddia_theorem.scala)
- [ ] Convert types & propositions in [Ddia.v](../../Lp2lc_coq/Active/Ddia.v) into [Ddia.lean](../../Lp2lc/Active/Ddia.lean) using rule in [Scaffold.md](../Scaffold.md),
- [ ] Discharge theorems in [Ddia.lean](../../Lp2lc/Active/Ddia.lean) using rule in [Discharge.md](../Discharge.md),
