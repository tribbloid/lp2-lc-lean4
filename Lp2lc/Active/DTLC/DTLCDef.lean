import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

open Lp2lc.Active.Util

namespace AST
section
variable (I : Impl)

mutual

/--
Source type syntax.

`primitive` classifies primitive bytecode values, `depFn` classifies functions
whose output annotation may depend on the input reference, and `top` is the
wildcard annotation accepted by any value.
-/
inductive Typ : Type where
| primitive -- `AnyVal` in Scala, accepts only primitive values
| depFn (tIn : Typ) (tOut : (arg : I.Index) → Typ) -- dependent function
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
| ref (s: I.Index) -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala)

/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.
-/
inductive Val : Type where
| primitive (repr : Data) -- most specific type is always `primitive`
| primitiveFn (body: (arg: Data) -> Trm ) -- most specific type is always `.depFn .primitive _`
| fn (body : (arg : I.Index) → Trm) -- most specific type is always `.depFn _ _`

end

end

section
variable {I : Impl}

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

def typeHint (self: Trm I) := TypeView.mk self

namespace TypeView

/-- Reads the optional annotation attached to the outer term constructor. -/
def get (view : @TypeView I) : Option (Typ I) :=
  match view.self with
  | typeHinted _ t => some t
  | _ => none

/-- Removes all optional type annotations from a term. -/
def eraseRecursively (view : @TypeView I) (self : Trm I := view.self) : Trm I :=
  match self with
  | typeHinted self _ => self.typeHint.eraseRecursively self
  | .val (.primitiveFn body) => .val (.primitiveFn fun arg => (body arg).typeHint.eraseRecursively (body arg))
  | .val (.fn body) => .val (.fn fun arg => (body arg).typeHint.eraseRecursively (body arg))
  | .apply fn arg => .apply (fn.typeHint.eraseRecursively fn) (arg.typeHint.eraseRecursively arg)
  | _ => self

/-- Predicate that all annotations have been removed from a term. -/
def IsErased (view : @TypeView I) (self : Trm I := view.self) : Prop :=
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

end AST.Val

namespace Runtime
open AST

class Env (I : Impl) where
  EvalPermission : Permission (AST.Val I)
  -- fuel: Nat -- this can't be used, ewww
  forVals: FBound I.Index (AST.Val I) EvalPermission
  canEvalAny: (v: AST.Val I) -> EvalPermission v

end Runtime

section
variable {I : Impl}

def SemanticTyp := (value : AST.Val I) -> Prop

variable [Runtime.Env I]

namespace AST.Val

/--
Decidable semantic membership of a value in a type annotation.

This checks the value head form and, for function values, the input annotation.
Dependent output annotations are checked later by compiling the function body
with a concrete compile-time argument reference.
-/
def CanBind (type : AST.Typ I) (value : AST.Val I) : Prop := -- TODO: can simplify by matching type and value at same level. TODO: return type can be SemanticTyp
  match type with
  | .top => true
  | .primitive =>
    match value with
    | .primitive _ => true
    | .primitiveFn _ => false
    | .fn _ => false
  | .depFn _ _ =>
    match value with
    | .primitive _ => false
    | .primitiveFn _ => true
    | .fn _ => true

end AST.Val

namespace AST.Trm

/--
Evaluates a source or compiled program by spending 1 fuel at each semantic
descent. Runtime evaluation uses `FBound I Val` for references and deliberately
does not inspect compile-time typing evidence.
-/
def eval (self : AST.Trm I) : MayTerminate (AST.Val I)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | typeHinted self _ => eval self fuel
    | .val value => .result value
    | .apply fn arg =>
    -- TODO: for tree crawling, we need a single function to get an IR that contains eval result and a proof that it won't break
      let anf := (eval fn fuel, eval arg fuel) -- ANF, atomic normal form
      match anf with
      | (.result (.primitiveFn body), .result (.primitive repr)) =>
        eval (body repr) fuel
      | (.result (.fn body), .result value) =>
        let fBound := Runtime.Env.forVals (I := I)
        let permission := Runtime.Env.canEvalAny (I := I) value
        eval (body (fBound.save value permission)) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .error
    | .ref refValue =>
      let fBound := Runtime.Env.forVals (I := I)
      .result (fBound.load refValue)

/--
An safe program may run out of runtime fuel, but it must not reach runtime
`error`. When a runtime value is produced, it must satisfy the precondition.
-/
def IsSafeBy (self : AST.Trm I) (precondition : @SemanticTyp I) : Prop :=
  ∀ fuel, match self.eval fuel with
  | .result value => precondition value
  | .error => false
  | .outOfFuel => true

def IsSafeUnder (self : AST.Trm I) (binding : Typ I) : Prop :=
  self.IsSafeBy (fun trm => trm.CanBind binding)

end AST.Trm
end

-- namespace Toy

-- end Toy

namespace Compiler

/--
only contains FBound for types

in the future we may have FBound for terms or values and a permission granter
for transparent fn only
-/
class Env (I : Impl) where
  forTyps: FBound I.Index (AST.Val I -> Prop) fun _ => True

end Compiler

section
open AST

variable {I : Impl}

/--
a compiled term with safety proof
-/
structure Program (I : Impl) (binding : Typ I) where
  trm: AST.Trm I
  safetyProof: [Runtime.Env I] -> trm.IsSafeUnder binding

variable [Compiler.Env I]

namespace AST.Trm

/--
Fuel-guarded compiler API for type-checking `Trm` syntax and erasing optional
type annotations.

`compile` does not evaluate the program. On success, it preserves the source
program shape: values remain values, references remain references, and
applications remain applications of recursively compiled subterms. The emitted
program differs from the source only by removing accepted annotations.

Compilation fails for malformed programs or incompatible annotations. In
particular, applications must compile both sides successfully, the function side
must have a function type, and the argument type must be compatible with the
function input type. Checking function bodies may use the compile-time
`Compiler.Env.forTyps` F-bound bridge to stand for a bound argument type; this is
separate from runtime value binding and never calls `eval`.

Fuel `0` returns `.outOfFuel`; every recursive descent consumes fuel.

Semantic typing is successful compilation, so this compiler is the executable
typing rule used by:
- `Typing`
- `IsAdequate`
- `IsComposable`
-/
def compile (trm : Trm I) (binding : Typ I) : MayTerminate (Program I binding) := sorry

def compileToTrm (trm : Trm I)
  (binding : Typ I := .top) -- default arg doesn't validate binding.
: MayTerminate (Trm I) := fun (fuel : Nat) =>
  let out := compile trm binding fuel
  match out with
  | .result v => Outcome.result v.trm
  | .error => .error
  | .outOfFuel => .outOfFuel

-- /-- Semantic typing predicate, defined as successful fuel-guarded compilation. -/
-- def Typing
--     (typ: Typ I) (trm : Trm I) (fuel : Nat) : Prop := -- TOOD: move trm to be after colon
--     let _trm := Trm.typeHinted trm typ
--     (compile _trm fuel).isResult

end AST.Trm

end

-- section ProofByLogicalRelation
-- variable {I : Impl}

-- namespace AST.Trm

-- -- /--
-- -- The adequacy conjecture of logical relation:

-- -- a successfully compiled term should always be safe.

-- -- This conjecture is independent from type erasure.
-- -- -/
-- -- def IsAdequate [Compiler.Env I] [Runtime.Env I]
-- --     (src : Trm I) (fuel : Nat) : Prop :=
-- --   match AST.Trm.compile src fuel with
-- --   | .result program => AST.Trm.IsSafe program src.typeHint.get fuel
-- --   | _ => true

-- /--
-- The fundamental conjecture of logical relation:

-- Compiled function must fulfil it's semantic obligation: given a compiled argument with compatible
-- input type, it must be able to apply on it to produce a new compiled term with
-- output type.

-- This conjecture is independent from adequacy & type erasure.
-- -/
-- def IsComposable [Compiler.Env I]
--  (fn : Trm I) (arg: Val I) (tIn : Typ I) (tOut : I.Index → Typ I) (fuel : Nat) : Prop :=
--   let fnHinted := Trm.typeHinted fn (.depFn tIn tOut)
--   let argHinted := Trm.typeHinted (.val arg) tIn
--   let fnResult := AST.Trm.compile fnHinted fuel
--   let argResult := AST.Trm.compile argHinted fuel
--   match fnResult, argResult with
--   | .result compiledFn, .result compiledArg =>
--     let fBound := Compiler.Env.forTyps (I := I)
--     let argRef := fBound.save tIn True.intro
--     let pineapplePen := Trm.typeHinted (Trm.apply compiledFn compiledArg) (tOut argRef)
--     ∃ moreFuel,
--       (AST.Trm.compile pineapplePen moreFuel).isResult
--   | _, _ => true

-- end AST.Trm

-- end ProofByLogicalRelation


end DTLC

end Lp2lc.Active
