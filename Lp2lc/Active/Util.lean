

import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev KIndex := Type
-- abbrev KData := Type

class Impl : Type 1 where
  Index : KIndex
  -- Data : KData

inductive Data where -- no constructor

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


-- class Store {I : KIndex} {V : Type} (self: I -> Option V) where
--   empty : I -> Option V := fun _ => none
--   save (v: V) : (I × (I -> Option V)) :=
--     let
--   load (i: I) :=

-- section KV
-- variable (String Value : Type)

-- def Env := String → Option Value
-- namespace Env
-- def empty : Env K V := fun _ => none
-- _
-- def set ( : Env) ( : String) ( : Value) : Env :=
-- σ x v
-- fun => if = then some else
-- y y x v σ y
-- @[simp] theorem set
-- _
-- same ( : Env) ( : String) ( : Value) :
-- σ x v
-- ( .set ) = some :=
-- σ x v x v by
-- simp [set]
-- @[simp] theorem set
-- _
-- other ( : Env) ( : String) ( : Value) ( : ≠ ) :
-- σ x y v h y x
-- ( .set ) = :=
-- σ x v y σ y by
-- h
-- simp [set, ]
-- end Env

-- end KV


/-- Fixed-bound bridge between a HOAS carrier and the syntax family it represents. -/
class FBound (I : KIndex) (V : Type) (P : Permission V): Type where -- fixed-point bound axiom, a crossover between de-bruijn Env/Store & HOAS carrier.
  save : (value : V) -> (permission: P value) → I -- `I` is unknown & there is no way to get `I` (required by HOAS binder) except submitting a `V`.
  load : (index : I) → V -- inverse of save
  roundtrip : ∀ (value : V), (permission : P value) → load (save value permission) = value

-- class Env (P: Index) (I : Index) (K : (index : Index) → Type) where
--   fBound : FBound I K
--   permission: P

attribute [simp] FBound.roundtrip

/-- Fuel-guarded semantic result used by executable interpreters and compilers. -/
inductive Outcome (T : KIndex)
| result (v: T)
| error
| outOfFuel

namespace Outcome

def isResult : (self : Outcome T) → Prop
| result _ => true
| _ => false

def isResultOrOutOfFuel : (self : Outcome T) → Prop
| error  => false
| _ => true

end Outcome

universe u v

def MayTerminate (T : Type) := (fuel: Nat) -> Outcome T

namespace MayTerminate
section
variable {T : Type}


def shouldYieldsWithFuel (self : MayTerminate T) (expectedV: T) : Prop :=
  ∃ (fuel : Nat), match (self fuel) with
  | .result v => v = expectedV
  | _ => false

def shouldYields (self : MayTerminate T) (expectedV: T) : Prop :=
  let hasFuel := self.shouldYieldsWithFuel expectedV
  let noFuel := self 0 = .outOfFuel
  hasFuel /\ noFuel

def shouldFail (self : MayTerminate T) : Prop :=
  let hasFuel := ∃ (fuel : Nat), match (self fuel) with
  | .error => true
  | _ => false
  let noFuel := self 0 = .outOfFuel
  hasFuel /\ noFuel

def isDecidable (self : MayTerminate T) : Prop :=
  ∃ (fuel : Nat), match (self fuel) with
  | .result _ => true
  | _ => false

def isSemiDecidable (self : MayTerminate T) : Prop :=
  ∀ (fuel: Nat), match (self fuel) with
  | .error  => false
  | _ => true

end
end MayTerminate

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
