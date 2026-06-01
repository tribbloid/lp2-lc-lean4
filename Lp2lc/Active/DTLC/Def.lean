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
variable (I : Index) -- AKA Symbol/Name/ID/Key

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

section
variable {I : Index} -- I as an implicit type argument, due to lean limitation the previous section cannot be merged into it without serious bloat, this is very lame

/-- Embeds values as value terms for dot-notation-friendly syntax construction. -/
instance valIsTrm : Coe (Val I) (Trm I) where
  coe := fun v => Trm.val v

namespace Typ

inductive SubtypeEv : (under: Typ I) -> (over: Typ I) -> Prop
| x2x (t: Typ I) : SubtypeEv t t
| x2Top (t : Typ I) : SubtypeEv t Typ.top

end Typ

namespace Trm

structure TypeView where (self: Trm I)

def type (self: Trm I) := TypeView.mk self

namespace TypeView

/-- Reads the optional annotation attached to the outer term constructor. -/
def get (view : @TypeView I) : Option (Typ I) :=
  match view.self with
  | .val _ t => t
  | .apply _ _ t => t
  | .ref _ t => t

/-- Replaces only the outer annotation while preserving the underlying term. -/
def update (view : @TypeView I) (t : Option (Typ I)) : Trm I :=
  match view.self with
  | .val value _ => .val value t
  | .apply fn arg _ => .apply fn arg t
  | .ref refValue _ => .ref refValue t

/-- Removes all optional type annotations from a term. -/
def eraseRecursively (view : @TypeView I) (self : Trm I := view.self) : Trm I :=
  match self with
  | .val (.fn body) _ => .val (.fn fun arg => (body arg).type.eraseRecursively (body arg)) none
  | .apply fn arg _ => .apply (fn.type.eraseRecursively fn) (arg.type.eraseRecursively arg) none
  | _ => self.type.update .none

/-- Predicate that all annotations have been removed from a term. -/
def IsErased (view : @TypeView I) (self : Trm I := view.self) : Prop :=
  let prior := self.type.get = none
  match self with
  | .val (.fn body) => prior ∧ ∀ arg, (body arg).type.IsErased (body arg)
  | .apply fn arg => prior ∧ fn.type.IsErased fn ∧ arg.type.IsErased arg
  | _ => prior

end TypeView

end Trm

end

end AST


inductive Symbol where -- no constructor, it can only be retrieved from FBound

namespace Symbolic

abbrev Typ := AST.Typ Symbol
abbrev Val := AST.Val Symbol
abbrev Trm := AST.Trm Symbol

end Symbolic

namespace Permission

class NotRequired {V : Type} (v: V) : Prop -- mk constructor can be used freely for any v

class Eval {I : Index} (v : AST.Val I) : Prop where
  private mk ::

end Permission

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

namespace Runtime
open AST

class Env (I : Index) where
  -- fuel: Nat -- this can't be used, ewww
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
  forTyps: FBound I AST.Typ Permission.NotRequired

end Compiletime

section
open AST

variable {I : Index} [Compiletime.Env I]

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
- adequacy lemma: (see `AdequacyGoal` definition)
- fundamental lemma: compatible compiled function and argument can be composed
  into program that preserves successful compilation
- soundness: semantic typing implies existence of a type-erased adequate
  compiled program
-/
def compile (trm : Trm I) (fuel : Nat) : Outcome (Trm I) := sorry

/-- Semantic typing predicate, defined as successful fuel-guarded compilation. -/
def Typing (trm : Trm I) (fuel : Nat) : Prop :=
  (compile trm fuel).isSome

end AST.Trm

end

namespace AST.Trm

/--
An adequate program may run out of runtime fuel, but it must not reach runtime
`error`. When runtime evaluation produces a value, that value must satisfy the
source annotation checked by compilation.
-/
private def IsAdequate_Runtime {I : Index} [Runtime.Env I] (program : Trm I) (fuel: Nat) : Prop :=
  match program.eval fuel with
  | .outOfFuel => true
  | .some result =>
    match program.type.get with
    | .some t => result.satisfies t -- result must satisfy type
    | .none => true -- program doesn't have type annotation, no need to verify the result
  | .error => false

/--
adequacy conjecture of logical relationship:

a successfully compiled term executes without runtime error, either
  producing a value satisfying the source annotation or running out of fuel
-/
def IsAdequate_Compiletime {I : Index} [Compiletime.Env I] [Runtime.Env I] (src : Trm I) (fuel : Nat) : Prop :=
  match src.compile fuel with
  | .some compiled =>
    compiled.IsAdequate_Runtime fuel
  | _ => true

/--
AKA the fundamental theorem of logical relation: compiled function
must fulfil it's semantic obligation: given a compiled argument with compatible type, it
must be able to execute on it and produce a
-/
def IsComposable {I : Index} [Compiletime.Env I]
 (pineapple pen : Trm I) (fuel : Nat) : Prop :=



end AST.Trm


end DTLC

end Lp2lc.Active
