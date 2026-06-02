import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

open Util

namespace Permission

class NotRequired (V : Type) (v: V) : Prop -- mk constructor can be used freely for any v

class Eval (V : Type) (v: V) : Prop where
  private mk ::

end Permission


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
-/

-- TODO: this definition has 2 problems: can eval at compiletime, cannot express
-- primitive fn that modify bytecode
inductive Trm : Index where
| typeHinted (self : Trm) (hint : Typ) -- AKA type annotation, each term can have 0, 1, or many hints (e.g. `((1: Tuple): Product): AnyRef`), required for fundamental/composability theorem
| val (v : Val) -- AKA literal
| apply (fn : Trm) (arg : Trm) -- fn must be a function that can be applied on arg
| ref (s: I) -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala)

/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.
-/
inductive Val : Index where
| primitive (repr : ByteCode) -- most specific type is always `primitive`
| primitiveFn (body: (arg: ByteCode) -> Trm ) -- most specific type is always `.depFn .primitive _`
| fn (body : (arg : I) → Trm) -- most specific type is always `.depFn _ _`

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
  | typeHinted _ t => some t
  | _ => none

/-- Removes all optional type annotations from a term. -/
def eraseRecursively (view : @TypeView I) (self : Trm I := view.self) : Trm I :=
  match self with
  | typeHinted self _ => self.type.eraseRecursively self
  | .val (.primitiveFn body) => .val (.primitiveFn fun arg => (body arg).type.eraseRecursively (body arg))
  | .val (.fn body) => .val (.fn fun arg => (body arg).type.eraseRecursively (body arg))
  | .apply fn arg => .apply (fn.type.eraseRecursively fn) (arg.type.eraseRecursively arg)
  | _ => self

/-- Predicate that all annotations have been removed from a term. -/
def IsErased (view : @TypeView I) (self : Trm I := view.self) : Prop :=
  match self with
  | typeHinted _ _ => false
  | .val (.primitiveFn body) => ∀ arg, (body arg).type.IsErased (body arg)
  | .val (.fn body) => ∀ arg, (body arg).type.IsErased (body arg)
  | .apply fn arg => fn.type.IsErased fn ∧ arg.type.IsErased arg
  | _ => true

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

namespace AST.Val

-- /--
-- Decidable semantic membership of a value in a type annotation.

-- This checks the value head form and, for function values, the input annotation.
-- Dependent output annotations are checked later by compiling the function body
-- with a concrete compile-time argument reference.
-- -/
-- def satisfies {I : Index} (value : Val I) (type : Typ I) : Bool :=
--   match type with
--   | .top => true
--   | .primitive =>
--     match value with
--     | .primitive _ => true
--     | .primitiveFn _ => false
--     | .fn _ => false
--   | .depFn _ _ =>
--     match value with
--     | .primitive _ => false
--     | .primitiveFn _ => true
--     | .fn _ => true

end AST.Val

namespace Runtime
open AST

class Env (I : Index) where
  -- fuel: Nat -- this can't be used, ewww
  forVals: FBound I AST.Val (Permission.Eval (AST.Val I))
  canEvalAny: (v: AST.Val I) -> Permission.Eval (AST.Val I) v

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
    | typeHinted self _ => eval self fuel
    | .val value => .result value
    | .apply fn arg =>
      let anf := (eval fn fuel, eval arg fuel) -- ANF, atomic normal form
      match anf with
      | (.result (.primitiveFn body), .result (.primitive repr)) =>
        eval (body repr) fuel
      | (.result (.fn body), .result value) =>
        let fBound := Runtime.Env.forVals (I := I)
        eval (body (fBound.save value (Runtime.Env.canEvalAny (I := I) value))) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .error
    | .ref refValue =>
      let fBound := Runtime.Env.forVals (I := I)
      .result (fBound.load refValue)

end AST.Trm
end

namespace Compiletime

/--
only contains FBound for types

in the future we may have FBound for terms or values and a permission granter
for transparent fn only
-/
class Env (I : Index) where
  forTyps: FBound I AST.Typ (Permission.NotRequired (AST.Typ I))

end Compiletime

section
open AST

variable {I : Index} [Compiletime.Env I]

namespace AST.Trm
/--
Fuel-guarded compiler API for compiling any `Trm` with optional type annotations
into semantic program (also a `Trm`, but type info are removed). Emits a runtime program that may or may not
be different.

It does not evaluate the program! compiling a `Trm.apply` should only results
the same or a slightly different `Trm.apply`.

This is the only public API for compilation, every other functions must be private.

- compiling malformed terms fails
- compiling terms with wrong annotations fails
- fuel `0` always returns `outOfFuel`
- compile-time checking must not call runtime `eval`
- application compilation may use the compile-time `FBound I Trm` binding to
  check the substituted function body
- when a compiled function carries an input annotation, application compilation
  checks that the compiled argument value satisfies that input annotation
- `FBound I Trm` represents compile-time bindings and is deliberately separate
  from `FBound I Val`, which represents runtime bindings

Semantic typing is successful fuel-guarded compilation, so this compiler is the
definition of the semantic typing rule.

This rule supports:
- adequacy lemma: (see `def IsAdequate`)
- fundamental lemma: (see `def IsComposable`)
- soundness theorem
-/
def compile (trm : Trm I) (fuel : Nat) : Outcome (Trm I) := sorry

/-- Semantic typing predicate, defined as successful fuel-guarded compilation. -/
def Typing (typ: Typ I) (trm : Trm I) (fuel : Nat) : Prop := -- TOOD: move trm to be after colon
    let _trm := Trm.typeHinted trm typ
    (compile _trm fuel).isDecidable

end AST.Trm

end

section ProofByLogicalRelation
variable {I : Index}

namespace AST.Trm

/--
An safe program may run out of runtime fuel, but it must not reach runtime
`error`. When a runtime value is produced with a type hint, the value must
compile under that hint.
-/
def IsSafe [Compiletime.Env I] [Runtime.Env I]
    (program : Trm I) (typeHint : Option (Typ I)) (fuel: Nat) : Prop :=
  match program.eval fuel, typeHint with
  | .result value, some type => ((Trm.typeHinted (.val value) type).compile fuel).isDecidable
  | result, _ => result.isSemiDecidable

/--
The adequacy conjecture of logical relation:

a successfully compiled term should always be safe.

This conjecture is independent from type erasure.
-/
def IsAdequate [Compiletime.Env I] [Runtime.Env I] (src : Trm I) (fuel : Nat) : Prop :=
  match src.compile fuel with
  | .result program => program.IsSafe src.type.get fuel
  | _ => true

/--
The fundamental conjecture of logical relation:

Compiled function must fulfil it's semantic obligation: given a compiled argument with compatible
input type, it must be able to apply on it to produce a new compiled term with
output type.

This conjecture is independent from adequacy & type erasure.
-/
def IsComposable [Compiletime.Env I]
 (fn : Trm I) (arg: Val I) (tIn : Typ I) (tOut : I → Typ I) (fuel : Nat) : Prop :=
  let fnHinted := Trm.typeHinted fn (.depFn tIn tOut)
  let argHinted := Trm.typeHinted (.val arg) tIn
  match fnHinted.compile fuel, argHinted.compile fuel with
  | .result compiledFn, .result compiledArg =>
    let fBound := Compiletime.Env.forTyps (I := I)
    let argRef := fBound.save tIn Permission.NotRequired.mk
    let pineapplePen := Trm.typeHinted (Trm.apply compiledFn compiledArg) (tOut argRef)
    ∃ moreFuel, (pineapplePen.compile moreFuel).isDecidable
  | _, _ => true

end AST.Trm

end ProofByLogicalRelation


end DTLC

end Lp2lc.Active
