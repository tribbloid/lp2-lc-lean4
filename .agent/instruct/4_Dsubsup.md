## Overview

You job is to convert Coq proof for DOT (Scala's type system) into Scala examples and Lean4 proof.

You are in a very safe, sandboxed environment. You can use gradle & lake to compile code at will.

## Tasks (continue from where they left off, mark as complete when done)

- [ ] Explain/Demo Scala language features defined as types in [Dsubsup.v](../../Lp2lc_coq/Active/Dsubsup.v) using rule in [Demo.md](../Demo.md), write Scala code into [Dsubsup.scala](../../example/src/main/scala/lp2lc/example/Dsubsup.scala)
- [ ] Explain theorems in [Dsubsup.v](../../Lp2lc_coq/Active/Dsubsup.v) using rule in [Explain.md](../Explain.md), write Scala code & comment into [Dsubsup_theorem.scala](../../example/src/main/scala/lp2lc/example/Dsubsup_theorem.scala)
- [ ] Convert types & propositions in [Dsubsup.v](../../Lp2lc_coq/Active/Dsubsup.v) into [Dsubsup.lean](../../Lp2lc/Active/Dsubsup.lean) using rule in [Scaffold.md](../Scaffold.md),
- [ ] Discharge theorems in [Dsubsup.lean](../../Lp2lc/Active/Dsubsup.lean) using rule in [Discharge.md](../Discharge.md),
