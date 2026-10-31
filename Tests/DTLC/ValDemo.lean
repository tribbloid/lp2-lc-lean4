import «Lp2lc».Active.DTLC.Serial.Def

namespace Tests.DTLC.Sanity

open Lp2lc.Active.DTLC
open Lp2lc.Active.Util

def bFalse := "false"

def bTrue := "true"

def vFalse : Val := .lit bFalse

def vTrue : Val := .lit bTrue

instance {n} : Coe (Val n) (Trm n) := ⟨Val.asTrm⟩

instance {n} (self : Val n) : CoeT (Val n) self (Trm n) := ⟨Val.asTrm self⟩

namespace Val

def idFn : AST 0 .val :=
  .fn .TLit (.mk (λ proxy => .ref proxy .same))

end Val

end Tests.DTLC.Sanity
