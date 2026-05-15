

import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

/-- Universe-1 carrier for PHOAS indices. -/
abbrev Index := Type

class FBound (I : Index) (K : Index -> Type) where -- fixed-point cast, looks like a reversed Env, it cast `Trm I` into something Val.depFn can accept
  fwd : K I -> I -- useful in eval, definition uses the inverse but interpreter is not allowed to see it.
  rev : I -> K I
  fwdRoundtrip : (value : K I) -> rev (fwd value) = value

attribute [simp] FBound.fwdRoundtrip

inductive Outcome (T : Index)
| some (v: T)
| error
| outOfFuel

namespace Outcome

def isSome : (self: Outcome T) -> Prop
| .some _ => true
| _ => false

end Outcome

def ByteCode := String

abbrev Name := String

end Util
