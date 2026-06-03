import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

open Lp2lc.Active.Util

class Impl where
  I : Index
  B : ByteCode


namespace AST
section
variable (impl : Impl)

mutual

/--
Source type syntax.

`primitive` classifies primitive bytecode values, `depFn` classifies functions
whose output annotation may depend on the input reference, and `top` is the
wildcard annotation accepted by any value.
-/
inductive Typ : Type where
| primitive -- `AnyVal` in Scala, accepts only primitive values
| depFn (tIn : Typ) (tOut : (arg : impl.I) → Typ) -- dependent function
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
inductive Trm : Type where
| typeHinted (self : Trm) (hint : Typ) -- AKA type annotation, each term can have 0, 1, or many hints (e.g. `((1: Tuple): Product): AnyRef`), required for fundamental/composability theorem
| val (v : Val) -- AKA literal
| apply (fn : Trm) (arg : Trm) -- fn must be a function that can be applied on arg
| ref (s: impl.I) -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala)

/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.
-/
inductive Val : Type where
| primitive (repr : impl.B) -- most specific type is always `primitive`
| primitiveFn (body: (arg: impl.B) -> Trm ) -- most specific type is always `.depFn .primitive _`
| fn (body : (arg : impl.I) → Trm) -- most specific type is always `.depFn _ _`

end

end

section
variable {impl : Impl}

/-- Embeds values as value terms for dot-notation-friendly syntax construction. -/
instance valIsTrm : Coe (Val impl) (Trm impl) where
  coe := fun v => Trm.val v

namespace Typ

inductive SubtypeEv : (under: Typ impl) -> (over: Typ impl) -> Prop
| x2x (t: Typ impl) : SubtypeEv t t
| x2Top (t : Typ impl) : SubtypeEv t Typ.top

end Typ

namespace Trm

structure TypeView where (self: Trm impl)

def typeHint (self: Trm impl) := TypeView.mk self

namespace TypeView

/-- Reads the optional annotation attached to the outer term constructor. -/
def get (view : @TypeView impl) : Option (Typ impl) :=
  match view.self with
  | typeHinted _ t => some t
  | _ => none

/-- Removes all optional type annotations from a term. -/
def eraseRecursively (view : @TypeView impl) (self : Trm impl := view.self) : Trm impl :=
  match self with
  | typeHinted self _ => self.typeHint.eraseRecursively self
  | .val (.primitiveFn body) => .val (.primitiveFn fun arg => (body arg).typeHint.eraseRecursively (body arg))
  | .val (.fn body) => .val (.fn fun arg => (body arg).typeHint.eraseRecursively (body arg))
  | .apply fn arg => .apply (fn.typeHint.eraseRecursively fn) (arg.typeHint.eraseRecursively arg)
  | _ => self

/-- Predicate that all annotations have been removed from a term. -/
def IsErased (view : @TypeView impl) (self : Trm impl := view.self) : Prop :=
  match self with
  | typeHinted _ _ => false
  | .val (.primitiveFn body) => ∀ arg, (body arg).typeHint.IsErased (body arg)
  | .val (.fn body) => ∀ arg, (body arg).typeHint.IsErased (body arg)
  | .apply fn arg => fn.typeHint.IsErased fn ∧ arg.typeHint.IsErased arg
  | _ => true

end TypeView

end Trm

end

end AST

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

class Env (impl : Impl) where
  EvalPermission : Permission (AST.Val impl)
  -- fuel: Nat -- this can't be used, ewww
  forVals: FBound impl.I (fun index => AST.Val { impl with I := index }) EvalPermission
  canEvalAny: (v: AST.Val impl) -> EvalPermission v

end Runtime

section
variable {impl : Impl}
variable [Runtime.Env impl]

namespace AST.Trm

/--
Evaluates a source or compiled program by spending 1 fuel at each semantic
descent. Runtime evaluation uses `FBound I Val` for references and deliberately
does not inspect compile-time typing evidence.
-/
def eval (self : AST.Trm impl) (fuel : Nat) : Outcome (AST.Val impl) :=
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
        let fBound := Runtime.Env.forVals (impl := impl)
        let evalPermission := Runtime.Env.canEvalAny value
        eval (body (fBound.save value evalPermission)) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .error
    | .ref refValue =>
      let fBound := Runtime.Env.forVals (impl := impl)
      .result (fBound.load refValue)

end AST.Trm
end

namespace Compiletime

/--
only contains FBound for types

in the future we may have FBound for terms or values and a permission granter
for transparent fn only
-/
class Env (impl : Impl) where
  TypPermission : Permission (AST.Typ impl)
  forTyps: FBound impl.I (fun index => AST.Typ { impl with I := index }) TypPermission
  canSaveAnyTyp: (typ: AST.Typ impl) -> TypPermission typ

end Compiletime

section
open AST

variable {impl : Impl}
variable [Compiletime.Env impl]

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
def compile (trm : Trm impl) (fuel : Nat) : Outcome (Trm impl) := sorry

/-- Semantic typing predicate, defined as successful fuel-guarded compilation. -/
def Typing
    (typ: Typ impl) (trm : Trm impl) (fuel : Nat) : Prop := -- TOOD: move trm to be after colon
    let _trm := Trm.typeHinted trm typ
    (compile _trm fuel).isDecidable

end AST.Trm

end

section ProofByLogicalRelation
variable {impl : Impl}

namespace AST.Trm

/--
An safe program may run out of runtime fuel, but it must not reach runtime
`error`. When a runtime value is produced with a type hint, the value must
compile under that hint.
-/
def IsSafe [Compiletime.Env impl] [Runtime.Env impl]
    (program : Trm impl) (typeHint : Option (Typ impl)) (fuel: Nat) : Prop :=
  let result := AST.Trm.eval program fuel
  match result, typeHint with
  | .result value, some type =>
    let hinted := Trm.typeHinted (.val value) type
    (AST.Trm.compile hinted fuel).isDecidable
  | result, _ => result.isSemiDecidable

/--
The adequacy conjecture of logical relation:

a successfully compiled term should always be safe.

This conjecture is independent from type erasure.
-/
def IsAdequate [Compiletime.Env impl] [Runtime.Env impl]
    (src : Trm impl) (fuel : Nat) : Prop :=
  match AST.Trm.compile src fuel with
  | .result program => AST.Trm.IsSafe program src.typeHint.get fuel
  | _ => true

/--
The fundamental conjecture of logical relation:

Compiled function must fulfil it's semantic obligation: given a compiled argument with compatible
input type, it must be able to apply on it to produce a new compiled term with
output type.

This conjecture is independent from adequacy & type erasure.
-/
def IsComposable [Compiletime.Env impl]
 (fn : Trm impl) (arg: Val impl) (tIn : Typ impl) (tOut : impl.I → Typ impl) (fuel : Nat) : Prop :=
  let fnHinted := Trm.typeHinted fn (.depFn tIn tOut)
  let argHinted := Trm.typeHinted (.val arg) tIn
  let fnResult := AST.Trm.compile fnHinted fuel
  let argResult := AST.Trm.compile argHinted fuel
  match fnResult, argResult with
  | .result compiledFn, .result compiledArg =>
    let fBound := Compiletime.Env.forTyps (impl := impl)
    let typPermission := Compiletime.Env.canSaveAnyTyp tIn
    let argRef := fBound.save tIn typPermission
    let pineapplePen := Trm.typeHinted (Trm.apply compiledFn compiledArg) (tOut argRef)
    ∃ moreFuel,
      (AST.Trm.compile pineapplePen moreFuel).isDecidable
  | _, _ => true

end AST.Trm

end ProofByLogicalRelation


end DTLC

end Lp2lc.Active
