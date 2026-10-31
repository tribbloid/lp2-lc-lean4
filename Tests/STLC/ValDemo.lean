import «Lp2lc».Active.STLC.Serial.Def

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Lp2lc.Active.Util

def bFalse := "false"

def bTrue := "true"

def vFalse : Val := .lit bFalse

def vTrue : Val := .lit bTrue

namespace Val

def idFn : AST 0 .val :=
  .fn .TLit (.mk (λ proxy => .ref proxy .same))

end Val

end Tests.STLC.Sanity
