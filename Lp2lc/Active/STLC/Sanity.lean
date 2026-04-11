import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC

namespace Trm

-- AKA intermediate representation (IR): reify the term in Lean.
-- map `_self` to a compatible lean type, e.g. Trm.function should be mapped to an actual lean function type
def Denotation (_self : Trm TrmVar) : Type := Trm TrmVar

-- AKA intermediate representation (IR): reify the term in Lean.
def denotation : (self : Trm TrmVar) -> self.Denotation :=
  fun self =>
    match self with
    | .var name declared => .var name declared
    | .function body => .function body
    | .apply fn arg => .apply (denotation fn) (denotation arg)

end Trm

namespace Sanity

-- contains verified examples and test cases of things in Def

-- All docstrings use short (under 5 lines) of Scala code as demonstrations.



end Sanity
