import «Lp2lc».Active.STLC_minimal.Serial.Def

namespace Tests.STLC_minimal.Sanity

open Lp2lc.Active.STLC_minimal
open Lp2lc.Active.Util

namespace Val

def idFn : AST 0 .val :=
  .fn .TLit (.mk (λ proxy => .ref proxy .same))

end Val

end Tests.STLC_minimal.Sanity
