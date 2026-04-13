import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC.Tests

namespace Trm


def trm1 (Index : Type) : _Trm Index :=
 sorry

def trm2 : ClosedTrm :=
 trm1

def trm3 (Index : Type) : _Trm Index :=
 trm2 Index

end Trm

end Tests
