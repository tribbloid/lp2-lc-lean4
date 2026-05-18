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
| primitive -- `AnyVal` in Scala
| depFn (tIn : Typ) (tOut : (arg : I) → Typ) -- dependent function
| top -- anything/wildcard type, can bind both primitive and depFn.

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
| fn (body : (arg : I) → Trm)  (tIn : Option Typ := by exact none)-- most specific type is always `.depFn`

end

/-- Embeds values as value terms for dot-notation-friendly syntax construction. -/
instance valIsTrm : Coe (Val I) (Trm I) where
  coe := fun v => Trm.val v

namespace Typ

/-- Checks whether one annotation is compatible with another at its semantic head form. -/
def compatible {I : Index} (actual : Typ I) (expected : Typ I) : Bool :=
  match actual, expected with
  | _, .top => true
  | .primitive, .primitive => true
  | .depFn (tIn := _) (tOut := _), .depFn (tIn := _) (tOut := _) => true
  | _, _ => false

end Typ

namespace Val

/--
Decidable semantic membership of a value in a type annotation.
Semantic typing predicate for values.
-/
def satisfies {I : Index} (value : Val I) (typeAnnotation : Typ I) : Bool :=
  match typeAnnotation with
  | .top => true
  | .primitive =>
    match value with
    | .primitive (repr := _) => true
    | .fn (body := _) (tIn := _) => false
  | .depFn (tIn := tIn) (tOut := _) =>
    match value with
    | .primitive (repr := _) => false
    | .fn (body := _) (tIn := none) => true
    | .fn (body := _) (tIn := some actual) => actual.compatible tIn

end Val

namespace Trm

/-- Reads the optional annotation attached to the outer term constructor. -/
def typeGet {I : Index} (self : Trm I) : Option (Typ I) :=
  match self with
  | .val (v := _) (t := typeAnnotation) => typeAnnotation
  | .apply (fn := _) (arg := _) (t := typeAnnotation) => typeAnnotation
  | .ref _ typeAnnotation => typeAnnotation

/-- Replaces only the outer annotation while preserving the underlying term. -/
def typeUpdate {I : Index} (self : Trm I) (typeAnnotation : Option (Typ I)) : Trm I :=
  match self with
  | .val (v := value) (t := _) => .val (v := value) (t := typeAnnotation)
  | .apply (fn := fn) (arg := arg) (t := _) => .apply (fn := fn) (arg := arg) (t := typeAnnotation)
  | .ref refValue _ => .ref refValue typeAnnotation

/-- Removes all optional type annotations from a term. -/
def typeEraseAll {I : Index} (self : Trm I) : Trm I :=
  match self with
  | .val (.primitive repr) _ => .val (.primitive repr) none
  | .val (.fn body _) _ => .val (.fn (body := fun arg => typeEraseAll (body arg)) (tIn := none)) none
  | .apply fn arg _ => .apply (typeEraseAll fn) (typeEraseAll arg) none
  | .ref refValue _ => .ref refValue none

/-- Predicate that all annotations have been removed from a term. -/
def TypeIsErased {I : Index} (self : Trm I) : Prop :=
  match self with
  | .val (.primitive _) t => t = none
  | .val (.fn body tIn) t => t = none ∧ tIn = none ∧ ∀ arg, (body arg).TypeIsErased
  | .apply fn arg t => t = none ∧ fn.TypeIsErased ∧ arg.TypeIsErased
  | .ref _ t => t = none

/-- Normalizes source terms to values while spending fuel at each semantic descent -/
def eval {I : Index} [FBound I Val] (trm : Trm I) (fuel : Nat) : Outcome (Val I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val value _ => .some value
    | .apply fn arg _ =>
      let anf := (fn.eval fuel, arg.eval fuel) -- ANF, atomic normal form
      match anf with
      | (.some (.fn body _), .some value) =>
        (body (FBound.fwd value)).eval fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .error
    | .ref refValue _ =>
      .some (FBound.rev refValue)

/--
fuel-guarded compiler API that verify a term (with optional type annotation),
and generate a more specialised, executable, type-erased term. Given enough
fuel, this execution should always succeed (adequency lemma).

- compiling malformed term will fail
- compiling term with wrong annotation will fail
- always return outOfFuel if fuel drops to 0
- evaluation in compiletime is strictly forbidden, and compilation must not call
  `eval`. Application compilation may use the compile-time `FBound I Trm`
  binding to compile-check the substituted function body, and it emits the
  resulting type-erased program; that emitted program may itself contain
  `Trm.apply`, but application compilation is not required to preserve `.apply`
  as the root constructor.
- The `FBound I Trm` condition (representing compile-time bindings) is
  deliberately different from `FBound I Val` (representing runtime bindings) to
  avoid calling `eval` during compilation.

semantic typing (a predicate on ) is merely this API being successful

this is a critical semantic rule for proving:

- adequecy lemma: a successfully compiled term can always be successfully
  executed (to a value that can be type-checked by the same type) or run out of
  fuel.
- fundamental lemma: if a type-annotated function and it's compatible argumennt
  can both be successfully compiled, then their applied form can also be
  successfull ccompiled.
- finally, soundness theorem that uses the above 2 lemma.
-/
def compile {I : Index} [FBound I Trm] (trm : Trm I) (fuel : Nat) : Outcome (Trm I) := sorry

/-- Semantic typing predicate exposed as successful fuel-guarded compilation. -/
def Typing {I : Index} [FBound I Trm] (trm : Trm I) (fuel : Nat) : Prop :=
  (trm.compile fuel).isSome

end Trm


end Syntax

/-- Closed polymorphic type syntax fixture over any PHOAS index. -/
abbrev TypAST := {I : Index} → Typ I

/-- Closed polymorphic value syntax fixture over any PHOAS index. -/
abbrev ValAST := {I : Index} → Val I

/-- Closed polymorphic term syntax fixture over any PHOAS index. -/
abbrev TrmAST := {I : Index} → Trm I

end DTLC

end Lp2lc.Active
