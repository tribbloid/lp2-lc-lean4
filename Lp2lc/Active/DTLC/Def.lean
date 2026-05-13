import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

universe u v

-- 1. Implicitly lift a type to a higher universe using ULift
/-- Coerce a lower-universe type into a higher universe through `ULift`. -/
instance _autoUliftType : Coe (Type u) (Type (max u v)) where
  coe := ULift

-- 2. Implicitly lift the values of that type into the ULift wrapper, these 2 enabled universe cumulativity in rocq
/-- Coerce a value into the `ULift` carrier chosen by the lifted type. -/
instance _autoUliftValue {α : Type u} : Coe α (ULift.{v, u} α) where
  coe := ULift.up

structure K : Type

abbrev K1: Type 1 := K

open Util

/-- Universe-1 carrier for PHOAS indices. -/
abbrev Index := Type

section Syntax

variable (I : Index) -- index


mutual

/--
Type AST
-/
inductive Typ : Index where
| primitive
| depFn (tIn : Typ) (tOut : (arg : I) -> Typ)
| top -- type of anything, can bind both primitive and depFn.

-- def TAnno := Option Typ -- doesn't work in mutual block

/--
Term AST

Each AST can have optional type annotations, but they are only extra
constraint used in type-checking.

In HOAS there is no Context/Env to bind type to terms, so an optional type
annotation is the only realistic alternative. It shouldn't be confused with
intrinsic typing, which is impossible for Typ in the same mutual block.

In runtime, type annotations are ideally erased.
-/
inductive Trm : Index where
| val (v : Val) (t : Option Typ := by exact none)
| apply (fn : Trm) (arg : Trm) (t : Option Typ := by exact none)
| ref (s: I) (t : Option Typ := by exact none) -- binded reference, AKA variable/var

/--
Value AST, contains no ref and apply.

Only eval target and only accepted input of ANF (atomic normal form)

In runtime, type annotations are ideally erased.
-/
inductive Val : Index where
| primitive (repr : ByteCode) -- most specific type is always `primitive`
| fn (body : (arg : I) -> Trm)  (tIn : Option Typ := by exact none)-- most specific type is always `.depFn`

end

namespace Trm

def IsTypeErased (self: Trm I): Prop :=
  match self with
  | .val (.primitive _) t => t = none
  | .val (.fn body tIn) t => t = none ∧ tIn = none ∧ ∀ arg, IsTypeErased (body arg)
  | .apply fn arg t => t = none ∧ IsTypeErased fn ∧ IsTypeErased arg
  | .ref _ t => t = none

/-- Removes all optional type annotations from a term. -/
def eraseType (self: Trm I): Trm I :=
  match self with
  | .val (.primitive repr) _ => .val (.primitive repr) none
  | .val (.fn body _) _ => .val (.fn (body := fun arg => (body arg).eraseType) (tIn := none)) none
  | .apply fn arg _ => .apply fn.eraseType arg.eraseType none
  | .ref s _ => .ref s none

/-- Erasing annotations always produces a type-erased term. -/
theorem eraseType_isErased : ∀ (self : Trm I), IsTypeErased I (eraseType I self)
| .val (.primitive _) _ => rfl
| .val (.fn body _) _ => ⟨rfl, rfl, fun arg => eraseType_isErased (body arg)⟩
| .apply fn arg _ => ⟨rfl, eraseType_isErased fn, eraseType_isErased arg⟩
| .ref _ _ => rfl

end Trm

namespace Val
end Val

instance valIsTrm : Coe (Val I) (Trm I) where
  coe := (fun v => Trm.val v)

end Syntax

abbrev TypAST := {I : Index} -> Typ I

abbrev ValAST := {I : Index} -> Val I

abbrev TrmAST := {I : Index} -> Trm I

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

/-- Normalizes source terms to values while spending fuel at each semantic descent -/
def Trm.eval {I : Index} [FBound I Val] (trm : Trm I) (fuel : Nat) : Outcome (Val I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val value _ => .some value
    | apply fn arg _ =>
      let anf := (fn.eval fuel, arg.eval fuel) -- ANF, atomic normal form
      match anf with
      | (.some (.fn body), .some value) => (body (FBound.fwd value)).eval fuel
      | (.outOfFuel, _) | (_, .outOfFuel)  => .outOfFuel
      | _ => .error
    | .ref s _ =>
      .some (FBound.rev s)

/--
fuel-guarded compiler API that verify a term (with optional type annotation),
and generate a more specialised, executable, type-erased term. This execution should always succeed (adequency lemma).

- compiling malformed term will fail
- compiling term with wrong annotation will fail
- always return outOfFuel if fuel drops to 0
- no term/application should be evaluated during compilation. The `FBound I Trm` condition (representing compiletime bindings) is deliberately different
  from `FBound I Val` (representing runtime binding) to avoid evaluation in compiletime.

semantic typing (a predicate on ) is merely this API being successful

this is a critical semantic rule for proving:

- adequecy lemma: a successfully compiled term can always be successfully executed (to
  a value that can be type-checked by the same type) or run out of fuel.
- fundamental lemma: if a type-annotated function and it's compatible argumennt
  can both be successfully compiled, then their applied form can also be
  successfull ccompiled.
- finally, soundness theorem that uses the above 2 lemma.
-/
def Trm.compile {I : Index} [FBound I Trm] (trm: Trm I) (fuel: Nat): Outcome (Trm I) :=
  sorry

def Trm.typing {I : Index} [FBound I Trm](fuel: Nat)  (trm: Trm I) : Prop :=
  (trm.compile fuel).isSome

end DTLC

end Lp2lc.Active
