

import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev Index := Type

/-- Fixed-bound bridge between a PHOAS carrier and the syntax family it represents. -/
class FBound (I : Index) (K : (index : Index) → Type) where -- fixed-point cast, looks like a reversed Env, it cast `Trm I` into something Val.depFn can accept
  fwd : (value : K I) → I -- useful in eval, definition uses the inverse but interpreter is not allowed to see it.
  rev : (index : I) → K I
  fwdRoundtrip : (value : K I) → rev (fwd value) = value

attribute [simp] FBound.fwdRoundtrip

/-- Fuel-guarded semantic result used by executable interpreters and compilers. -/
inductive Outcome (T : Index)
| some (v: T)
| error
| outOfFuel

namespace Outcome

def isSome : (self : Outcome T) → Prop
| .some _ => true
| _ => false

end Outcome

def ByteCode := String
universe u v

-- 1. Implicitly lift a type to a higher universe using ULift
/-- Coerce a lower-universe type into a higher universe through `ULift`. -/
instance _autoUliftType : Coe (Type u) (Type (max u v)) where
  coe := ULift

-- 2. Implicitly lift the values of that type into the ULift wrapper, these 2 enabled universe cumulativity in rocq
/-- Coerce a value into the `ULift` carrier chosen by the lifted type. -/
instance _autoUliftValue {α : Type u} : Coe α (ULift.{v, u} α) where
  coe := ULift.up
abbrev Name := String

end Util
