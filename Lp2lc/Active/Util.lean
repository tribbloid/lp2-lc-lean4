

import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev Index := Type

/--
single-use permission to save v into FBound. The permission is for v only and won't work for other value

in runtime, permission to eval is granted for all values

in compiletime, no permission will be granted, you can only save Typ into FBound.

in the future we may:
- let transparent inline function carrying their own permission, so they can eval in compiletime and interact with typing
- add permission to load value From FBound
-/
def Permission (T : Type) := (v: T) -> Prop -- no instance will be provided ever, they are requiremennts to apply AST rules.

-- namespace Permission

-- -- class PermissionToCompile extends Permission
-- def Eval := Permission

-- -- def Eval := Permission

-- end Permission

/-- Fixed-bound bridge between a HOAS carrier and the syntax family it represents. -/
class FBound (I : Index) (K : (index : Index) → Type) (P : Permission (K I)): Type where -- fixed-point bound axiom, a crossover between de-bruijn Env/Store & HOAS carrier.
  save : (value : K I) -> (permission: P value) → I -- `I` is unknown & there is no way to get `I` (required by HOAS binder) except submitting a `K I`.
  load : (index : I) → K I -- inverse of save
  roundtrip : ∀ (value : K I), (permission : P value) → load (save value permission) = value

-- class Env (P: Index) (I : Index) (K : (index : Index) → Type) where
--   fBound : FBound I K
--   permission: P

attribute [simp] FBound.roundtrip

/-- Fuel-guarded semantic result used by executable interpreters and compilers. -/
inductive Outcome (T : Index)
| result (v: T)
| error
| outOfFuel

namespace Outcome

def isDecidable : (self : Outcome T) → Prop
| result _ => true
| _ => false

def isSemiDecidable : (self : Outcome T) → Prop
| error  => false
| _ => true

end Outcome

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
