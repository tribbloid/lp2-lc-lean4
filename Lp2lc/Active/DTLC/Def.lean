import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

open Util

namespace AST
section

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

-- TODO: this definition has 2 problems: can eval at compiletime, cannot express
-- primitive fn that modify bytecode
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
end

/-- Embeds values as value terms for dot-notation-friendly syntax construction. -/
instance valIsTrm : Coe (Val I) (Trm I) where
  coe := fun v => Trm.val v

namespace Typ

inductive SubtypeEv : (under: Typ I) -> (over: Typ I) -> Prop
| x2x (t: Typ I) : SubtypeEv t t
| x2Top (t : Typ I) : SubtypeEv t Typ.top

end Typ


namespace Trm

/-- Reads the optional annotation attached to the outer term constructor. -/
def typeGet {I : Index} (self : Trm I) : Option (Typ I) :=
  match self with
  | .val _ typeAnnotation => typeAnnotation
  | .apply _ _ typeAnnotation => typeAnnotation
  | .ref _ typeAnnotation => typeAnnotation

/-- Replaces only the outer annotation while preserving the underlying term. -/
def typeUpdate {I : Index} (self : Trm I) (typeAnnotation : Option (Typ I)) : Trm I :=
  match self with
  | .val value _ => .val value typeAnnotation
  | .apply fn arg _ => .apply fn arg typeAnnotation
  | .ref refValue _ => .ref refValue typeAnnotation

/-- Removes all optional type annotations from a term. -/
def typeEraseRecursively {I : Index} (self : Trm I) : Trm I :=
  match self with
  | .val (.fn body) _ => .val (.fn fun arg => typeEraseRecursively (body arg)) none
  | .apply fn arg _ => .apply (typeEraseRecursively fn) (typeEraseRecursively arg) none
  | _ => typeUpdate self .none

/-- Predicate that all annotations have been removed from a term. -/
def TypeIsErased {I : Index} (self : Trm I) : Prop :=
  let prior := typeGet self = none
  match self with
  | .val (.fn body) => prior ∧ ∀ arg, (body arg).TypeIsErased
  | .apply fn arg => prior ∧ fn.TypeIsErased ∧ arg.TypeIsErased
  | _ => prior

end Trm
end AST


namespace Closed

/-- Closed polymorphic type syntax fixture over any PHOAS index. -/
abbrev TypAST := {I : Index} → AST.Typ I

/-- Closed polymorphic value syntax fixture over any PHOAS index. -/
abbrev ValAST := {I : Index} → AST.Val I

/-- Closed polymorphic term syntax fixture over any PHOAS index. -/
abbrev TrmAST := {I : Index} → AST.Trm I


end Closed


namespace Val


end Val

namespace Permission

class NotRequired {V : Type} (v: V) : Prop -- mk constructor can be used freely for any v

class Eval {I : Index} (v : AST.Val I) : Prop where
  private mk ::

end Permission


namespace Runtime
open AST

class Env (I : Index) where
  forVals: FBound I AST.Val (Permission.Eval (I := I))
  canEvalAny: (v: AST.Val I) -> Permission.Eval v

end Runtime

section
variable {I : Index} [Runtime.Env I]

namespace AST.Trm

/--
Evaluates a source or compiled program by spending 1 fuel at each semantic
descent. Runtime evaluation uses `FBound I Val` for references and deliberately
does not inspect compile-time typing evidence.
-/
def eval (self : AST.Trm I) (fuel : Nat) : Outcome (AST.Val I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value _ => .some value
    | .apply fn arg _ =>
      let anf := (eval fn fuel, eval arg fuel) -- ANF, atomic normal form
      match anf with
      | (.some (.fn body), .some value) =>
        let fBound := Runtime.Env.forVals (I := I)
        eval (body (fBound.save value (Runtime.Env.canEvalAny (I := I) value))) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .error
    | .ref refValue _ =>
      let fBound := Runtime.Env.forVals (I := I)
      .some (fBound.load refValue)

end AST.Trm
end



namespace Compiletime

/--
only contains FBound for types

in the future we may have FBound for terms or values and a permission granter
for transparent fn only
-/
class Env (I : Index) where
  forTyps: FBound I Typ Permission.NotRequired

end Compiletime


section
open AST

variable {I : Index} [Compiletime.Env I]


namespace AST.Val

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
    | .primitive _ => true
    | .fn _ => false
  | .depFn _ _ =>
    match value with
    | .primitive _ => false
    | .fn _ => true

end AST.Val

namespace AST.Trm
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
def compile (trm : Trm I) (fuel : Nat) : Outcome (Trm I) :=
  let typeCompatible (under : Typ I) (over : Typ I) : Bool :=
    match under, over with
    | _, .top => true
    | .primitive, .primitive => true
    | .depFn _ _, .depFn _ _ => true
    | _, _ => false
  let rec compileWithType (boundType : Option (Typ I)) (trm : Trm I) (fuel : Nat) :
      Outcome (Trm I × Typ I) :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match trm with
      | .val value typeAnnotation =>
        let inferredType :=
          match value with
          | .primitive _ => Typ.primitive
          | .fn body =>
            Typ.depFn
              Typ.top
              (fun arg =>
                match compileWithType none (body arg) fuel with
                | .some (_, type) => type
                | _ => Typ.top)
        match typeAnnotation with
        | some type =>
          match value, type with
          | .fn body, .depFn tIn tOut =>
            let fBound := Compiletime.Env.forTyps (I := I)
            let argRef := fBound.save tIn Permission.NotRequired.mk
            match compileWithType (some tIn) (body argRef) fuel with
            | .some (_, bodyType) =>
              if typeCompatible bodyType (tOut argRef) then
                .some ((Trm.val value none).typeEraseRecursively, type)
              else
                .error
            | .outOfFuel => .outOfFuel
            | .error => .error
          | _, _ =>
            if value.satisfies type then
              .some ((Trm.val value none).typeEraseRecursively, type)
            else
              .error
        | none => .some ((Trm.val value none).typeEraseRecursively, inferredType)
      | .apply fn arg _ =>
        match compileWithType boundType fn fuel, compileWithType boundType arg fuel with
        | .some (compiledFn, fnType), .some (compiledArg, argType) =>
          match fnType with
          | .primitive => .error
          | .top => .error
          | .depFn tIn tOut =>
            if typeCompatible argType tIn then
              let fBound := Compiletime.Env.forTyps (I := I)
              let argRef := fBound.save argType Permission.NotRequired.mk
              match fn with
              | .val (.fn body) _ =>
                match compileWithType (some argType) (body argRef) fuel with
                | .some (_, resultType) =>
                  .some (.apply compiledFn compiledArg none, resultType)
                | .outOfFuel =>
                  .some (.apply compiledFn compiledArg none, tOut argRef)
                | .error => .error
              | _ =>
                .some (.apply compiledFn compiledArg none, tOut argRef)
            else
              .error
        | .outOfFuel, _ => .outOfFuel
        | _, .outOfFuel => .outOfFuel
        | _, _ => .error
      | .ref refValue _ =>
        .some (Trm.ref refValue none, boundType.getD Typ.top)
  match compileWithType none trm fuel with
  | .some (compiledTrm, _) => .some compiledTrm
  | .error => .error
  | .outOfFuel => .outOfFuel

/-- Semantic typing predicate, defined as successful fuel-guarded compilation. -/
def Typing (trm : Trm I) (fuel : Nat) : Prop :=
  (compile trm fuel).isSome

end AST.Trm

end

end DTLC

end Lp2lc.Active
