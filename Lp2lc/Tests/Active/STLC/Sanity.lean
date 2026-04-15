import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC.Tests

open Lp2lc.Active.STLC

namespace Trm

def trm1 (Index : Type) : Trm Index :=
 .literal ""

def trm2 : Closed Trm := trm1 -- eta-expansion happens automatically

def trm3 (Index : Type) : Trm Index :=
 trm2 Index

end Trm

end Tests
