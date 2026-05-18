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
Source type syntax.

`primitive` classifies primitive bytecode values, `depFn` classifies functions
whose output annotation may depend on the input reference, and `top` is the
wildcard annotation accepted by any value.
-/
inductive Typ : Index where
| primitive -- `AnyVal` in Scala, accepts only primitive values
| depFn (tIn : Typ) (tOut : (arg : I) → Typ) -- dependent function
| top -- anything/wildcard type, can accept any value.

-- def TAnno := Option Typ -- doesn't work in mutual block TODO: notation

/--
Source term syntax.

Each constructor may carry an optional type annotation. Annotations are
compile-time constraints only: compilation checks them and runtime evaluation
ignores them.

In HOAS there is no context or environment binding terms to types, so optional
annotations are the extrinsic typing evidence available to the compiler. They
are not intrinsic typing indices on terms.

`Trm.compile` checks annotations and emits an annotation-erased runtime program.
-/
inductive Trm : Index where
| val (v : Val) (t : Option Typ := by exact none)
| apply (fn : Trm) (arg : Trm) (t : Option Typ := by exact none)
| ref (s: I) (t : Option Typ := by exact none) -- binded reference, AKA variable/var

/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Function input annotations are compile-time constraints. They are checked by
compilation, may guide application checking, and are erased from compiled
programs.
-/
inductive Val : Index where
| primitive (repr : ByteCode) -- most specific type is always `primitive`
| fn (body : (arg : I) → Trm) -- most specific type is always `.depFn`

end

/-- Embeds values as value terms for dot-notation-friendly syntax construction. -/
instance valIsTrm : Coe (Val I) (Trm I) where
  coe := fun v => Trm.val v

namespace Typ

/-- Checks whether an actual annotation is accepted by an expected annotation. -/
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

This checks the value head form and, for function values, the input annotation.
Dependent output annotations are checked later by compiling the function body
with a concrete compile-time argument reference.
-/
def satisfies {I : Index} (value : Val I) (type : Typ I) : Bool :=
  match type with
  | .top => true
  | .primitive =>
    match value with
    | .primitive (repr := _) => true
    | .fn (body := _) => false
  | .depFn (tIn := _) (tOut := _) =>
    match value with
    | .primitive (repr := _) => false
    | .fn _ => true

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
  | .val (.fn body) _ => .val (.fn (body := fun arg => typeEraseAll (body arg))) none
  | .apply fn arg _ => .apply (typeEraseAll fn) (typeEraseAll arg) none
  | .ref refValue _ => .ref refValue none

/-- Predicate that all annotations have been removed from a term. -/
def TypeIsErased {I : Index} (self : Trm I) : Prop :=
  match self with
  | .val (.primitive _) t => t = none
  | .val (.fn body) t => t = none ∧ ∀ arg, (body arg).TypeIsErased
  | .apply fn arg t => t = none ∧ fn.TypeIsErased ∧ arg.TypeIsErased
  | .ref _ t => t = none

/--
Evaluates a source or compiled program by spending 1 fuel at each semantic
descent. Runtime evaluation uses `FBound I Val` for references and deliberately
does not inspect compile-time typing evidence.
-/
def eval {I : Index} [FBound I Val] (trm : Trm I) (fuel : Nat) : Outcome (Val I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val value _ => .some value
    | .apply fn arg _ =>
      let anf := (fn.eval fuel, arg.eval fuel) -- ANF, atomic normal form
      match anf with
      | (.some (.fn body), .some value) =>
        (body (FBound.fwd value)).eval fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .error
    | .ref refValue _ =>
      .some (FBound.rev refValue)

/--
Fuel-guarded compiler API for compiling any `Trm` with optional type annotations
into semantic program (also a `Trm`, but type info are removed).

It does not evaluate the program! compiling a `Trm.apply` should only results
the same or a slightly different `Trm.apply`.

This is the only public API for compilation, every other functions must be private.

Compilation checks optional annotations and emits a type-erased program for
runtime evaluation.

- compiling malformed terms fails
- compiling terms with wrong annotations fails
- fuel `0` always returns `outOfFuel`
- compile-time checking must not call runtime `eval`
- application compilation may use the compile-time `FBound I Trm` binding to
  check the substituted function body
- the emitted program is required to be type-erased, but application compilation
  is not required to preserve `.apply` as the root constructor
- when a compiled function carries an input annotation, application compilation
  checks that the compiled argument value satisfies that input annotation
- `FBound I Trm` represents compile-time bindings and is deliberately separate
  from `FBound I Val`, which represents runtime bindings

Semantic typing is successful fuel-guarded compilation, so this compiler is the
definition of the semantic typing rule.

This rule supports:
- adequacy: a successfully compiled term executes without runtime error, either
  producing a value satisfying the source annotation or running out of fuel
- fundamental lemma: compatible compiled function application preserves
  successful compilation
- soundness: semantic typing implies existence of a type-erased adequate
  compiled program
-/
def compile {I : Index} [FBound I Trm] (trm : Trm I) (fuel : Nat) : Outcome (Trm I) := sorry

/-- Semantic typing predicate, defined as successful fuel-guarded compilation. -/
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
