import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.DTLC.Def

namespace Lp2lc.Active

namespace DTLC

open AST
open Util

namespace AST.Trm

theorem adequacyLemma {I : Index} [Compiletime.Env I] [Runtime.Env I]
    (src : Trm I) (fuel : Nat)
    (isSafe :
      ∀ program, src.compile fuel = .result program → program.IsSafe src.type.get fuel) :
    src.IsAdequate fuel := by
  unfold IsAdequate
  cases h : src.compile fuel with
  | result program =>
    exact isSafe program h
  | error =>
    trivial
  | outOfFuel =>
    trivial

end AST.Trm

end DTLC

end Lp2lc.Active
