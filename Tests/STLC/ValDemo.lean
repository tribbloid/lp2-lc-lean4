import «Tests».STLC.Fixture

namespace Tests.STLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.STLC

/--
it is deliberately unconstructable: a fixpoint can hypothetically make it but this is not deliberately provided anywhere

test cases are expected to use the left inverse to demonstrate syntax rules
-/
inductive Symbol where

namespace Symbolic

variable [testEnv : TestEnv]

abbrev I : Parameters := refs.ExeParameters

abbrev Typ := AST.Typ I
abbrev Val := AST.Val I
abbrev Trm := ∀ {B : UIdU}, AST.Trm { F := refs.uid2val.UId, B := B, D := refs.D }

end Symbolic

open Tests.STLC.Sanity.Symbolic

variable [testEnv : TestEnv]

namespace Val

def idFn : Val :=
  .lam (λ x => .ref (.inr x)) .primitive

end Val

end Sanity
