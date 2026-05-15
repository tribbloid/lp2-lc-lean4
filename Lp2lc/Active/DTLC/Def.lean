import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

open Util

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

/-- Reads the optional annotation attached to the outer term constructor. -/
def type_get {I : Index} (self : Trm I) : Option (Typ I) :=
  match self with
  | .val (v := _) (t := type_annotation) => type_annotation
  | .apply (fn := _) (arg := _) (t := type_annotation) => type_annotation
  | Trm.ref _ type_annotation => type_annotation

/-- Replaces only the outer annotation while preserving the underlying term. -/
def type_update {I : Index} (self : Trm I) (type_annotation : Option (Typ I)) : Trm I :=
  match self with
  | .val (v := value) (t := _) => .val (v := value) (t := type_annotation)
  | .apply (fn := fn) (arg := arg) (t := _) => .apply (fn := fn) (arg := arg) (t := type_annotation)
  | Trm.ref ref_value _ => Trm.ref ref_value type_annotation

/-- Removes all optional type annotations from a term. -/
def type_eraseAll {I : Index} (self: Trm I): Trm I :=
  match self with
  | .val (.primitive repr) _ => .val (.primitive repr) none
  | .val (.fn body _) _ => .val (.fn (body := fun arg => type_eraseAll (body arg)) (tIn := none)) none
  | .apply fn arg _ => .apply (type_eraseAll fn) (type_eraseAll arg) none
  | .ref s _ => .ref s none

def type_IsErased {I : Index} (self: Trm I): Prop :=
  match self with
  | .val (.primitive _) t => t = none
  | .val (.fn body tIn) t => t = none ∧ tIn = none ∧ ∀ arg, type_IsErased (body arg)
  | .apply fn arg t => t = none ∧ type_IsErased fn ∧ type_IsErased arg
  | .ref _ t => t = none

/-- Normalizes source terms to values while spending fuel at each semantic descent -/
def eval {I : Index} [FBound I Val] (trm : Trm I) (fuel : Nat) : Outcome (Val I) :=
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


/-- Checks whether one annotation is compatible with another at its semantic head form. -/
def typeCompatible {I : Index} (actual : Typ I) (expected : Typ I) : Bool :=
  match actual, expected with
  | _, .top => true
  | .primitive, .primitive => true
  | .depFn (tIn := _) (tOut := _), .depFn (tIn := _) (tOut := _) => true
  | _, _ => false

/--
Decidable semantic membership of a value in a type annotation.
Semantic typing predicate for values.
-/
def valueSatisfies {I : Index} (value : Val I) (type_annotation : Typ I) : Bool :=
  match type_annotation with
  | .top => true
  | .primitive =>
    match value with
    | .primitive (repr := _) => true
    | .fn (body := _) (tIn := _) => false
  | .depFn (tIn := tIn) (tOut := _) =>
    match value with
    | .primitive (repr := _) => false
    | .fn (body := _) (tIn := none) => true
    | .fn (body := _) (tIn := some actual) => typeCompatible actual tIn


/-- Checks a value annotation and emits erased value syntax when it succeeds. -/
def compileValue {I : Index} (value : Val I) (type_annotation : Option (Typ I)) : Outcome (Trm I) :=
  match type_annotation with
  | none => .some (v := type_eraseAll (Trm.val (v := value) (t := none)))
  | some type_annotation =>
    match valueSatisfies value type_annotation with
    | true => .some (v := type_eraseAll (Trm.val (v := value) (t := none)))
    | false => .error


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
def compile {I : Index} [FBound I Trm] (trm: Trm I) (fuel: Nat): Outcome (Trm I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val (v := value) (t := type_annotation) =>
      compileValue value type_annotation
    | .apply (fn := fn) (arg := arg) (t := type_annotation) =>
      let anf := (fn.compile fuel, arg.compile fuel)
      match anf with
      | (.some (.val (.fn body _) _), .some compiled_arg) =>
        (type_update (body (FBound.fwd compiled_arg)) type_annotation).compile fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .error
    | Trm.ref ref_value type_annotation =>
      (type_update (FBound.rev (K := Trm) ref_value) type_annotation).compile fuel

def typing {I : Index} [FBound I Trm](fuel: Nat)  (trm: Trm I) : Prop :=
  (trm.compile fuel).isSome

/-- Adequacy predicate relating successful compilation to fuel-guarded execution. -/
def adequate {I : Index} [FBound I Val] (source : Trm I) (compiled : Trm I)
    (fuel : Nat) : Prop :=
  compiled.eval fuel ≠ .error ∧
    ∀ checked_type value,
      type_get source = some checked_type ->
      compiled.eval fuel = .some (v := value) ->
        valueSatisfies value checked_type = true

end Trm

instance valIsTrm : Coe (Val I) (Trm I) where
  coe := (fun v => Trm.val v)

end Syntax

abbrev TypAST := {I : Index} -> Typ I

abbrev ValAST := {I : Index} -> Val I

abbrev TrmAST := {I : Index} -> Trm I

end DTLC

end Lp2lc.Active
