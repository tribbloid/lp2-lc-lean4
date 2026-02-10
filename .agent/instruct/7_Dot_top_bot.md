## Overview

You job is to convert Coq proof for DOT (Scala's type system) into Scala examples and Lean4 proof.

You are in a very safe, sandboxed environment. You can use gradle & lake to compile code at will.

## Tasks (continue from where they left off, mark as complete when done)

- [ ] Explain/Demo Scala language features defined as types in [Dot_top_bot.v](../../Lp2lc_coq/Active/Dot_top_bot.v) using rule in [Demo.md](../Demo.md), write Scala code into [Dot_top_bot.scala](../../example/src/main/scala/lp2lc/example/Dot_top_bot.scala)
- [ ] Explain theorems in [Dot_top_bot.v](../../Lp2lc_coq/Active/Dot_top_bot.v) using rule in [Explain.md](../Explain.md), write Scala code & comment into [Dot_top_bot_theorem.scala](../../example/src/main/scala/lp2lc/example/Dot_top_bot_theorem.scala)
- [ ] Convert types & propositions in [Dot_top_bot.v](../../Lp2lc_coq/Active/Dot_top_bot.v) into [Dot_top_bot.lean](../../Lp2lc/Active/Dot_top_bot.lean) using rule in [Scaffold.md](../Scaffold.md),
- [ ] Discharge theorems in [Dot_top_bot.lean](../../Lp2lc/Active/Dot_top_bot.lean) using rule in [Discharge.md](../Discharge.md),
