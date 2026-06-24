import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

open Lp2lc.Active.Util

section variable {I : Free}

namespace AST
section variable (I : Free)

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
| primitive (repr : I.Data) -- most specific type is always `primitive`
| primitiveFn (body: (arg: I.Data) -> Trm ) -- most specific type is always `.depFn .primitive _`
| fn (body : (arg : I.Index) → Trm) -- most specific type is always `.depFn _ _`

end

abbrev Condition := (value : AST.Val I) -> Prop -- AKA semantic type
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

end AST

namespace AST.Val

end AST.Val

namespace Runtime
class Env where
  EvalPermission : Permission (AST.Val I)
  -- fuel: Nat -- this can't be used, ewww
  forVals: FBound I.Index { value : AST.Val I // EvalPermission value }
  canEvalAny: (v: AST.Val I) -> EvalPermission v

end Runtime

section variable [env: @Runtime.Env I]

namespace AST.Trm

/--
Evaluates a source or compiled program by spending 1 fuel at each semantic
descent. Runtime evaluation uses `FBound I Val` for references and deliberately
does not inspect compile-time typing evidence.
-/
def eval (self : AST.Trm I) : RecOption (AST.Val I)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | typeHinted self _ => eval self fuel
    | .val value => .yield (some value)
    | .apply fn arg =>
    -- TODO: for tree crawling, we need a single function to get an IR that contains eval result and a proof that it won't break
      let anf := (eval fn fuel, eval arg fuel) -- ANF, atomic normal form
      match anf with
      | (.yield (some (.primitiveFn body)), .yield (some (.primitive repr))) =>
        eval (body repr) fuel
      | (.yield (some (.fn body)), .yield (some value)) =>
        let fBound := env.forVals
        let permission := Runtime.Env.canEvalAny value
        eval (body (fBound.save (p := ()) ⟨value, permission⟩)) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref i =>
      let fBound := Runtime.Env.forVals
      .yield (some (fBound.load (p := ()) i).1)

/--
An safe program may run out of runtime fuel, but it must not reach runtime
`error`. When a runtime value is produced, it must satisfy the condition.
-/
def IsSafeBy (self : AST.Trm I) (condition : Condition I) : Prop :=
  ∀ fuel, match self.eval fuel with
  | .yield (some value) => condition value
  | .yield none => false
  | .outOfFuel => true

end AST.Trm

namespace AST.Val

/--
Semantic membership of a value in a type annotation.

Function values must satisfy their body obligation at the same runtime reference
that application evaluation will allocate for the argument.
-/
def CanBind (type : AST.Typ I) (value : AST.Val I) : Prop :=
  match type, value with
  | .top, _ => true
  | .primitive, .primitive _ => true
  | .primitive, .primitiveFn _ => false
  | .primitive, .fn _ => false
  | .depFn _tIn _tOut, .primitive _ => false
  | .depFn tIn tOut, .primitiveFn body =>
    ∀ repr,
      let arg := AST.Val.primitive repr
      arg.CanBind tIn →
        let fBound := Runtime.Env.forVals
        let permission := Runtime.Env.canEvalAny arg
        (body repr).IsSafeBy
          (fun value => value.CanBind (tOut (fBound.save (p := ()) ⟨arg, permission⟩)))
  | .depFn tIn tOut, .fn body =>
    ∀ arg,
      arg.CanBind tIn →
        let fBound := Runtime.Env.forVals
        let permission := Runtime.Env.canEvalAny arg
        (body (fBound.save (p := ()) ⟨arg, permission⟩)).IsSafeBy
          (fun value => value.CanBind (tOut (fBound.save (p := ()) ⟨arg, permission⟩)))

end AST.Val

namespace AST.Trm

def IsSafeUnder (self : AST.Trm I) (binding : Typ I) : Prop :=
  self.IsSafeBy (fun trm => trm.CanBind binding)

end AST.Trm

/--
a compiled term with safety proof
-/
structure Program (condition : AST.Condition I) where
  trm: AST.Trm I
  isSafe: trm.IsSafeBy condition

namespace Compiler

/--
Contains compile-time FBound bridges for semantic obligations.
-/
class Env where
  forSemantic: FBound I.Index { _semantic : AST.Val I -> AST.Condition I // True }

end Compiler

section variable [@Compiler.Env I]
open AST



namespace AST.Trm

/--
Fuel-guarded compiler API for recursively type-checking `Trm` syntax and return the same
`Trm` with it's safety proof, it does not evaluate the program.

It's very similar to `Trm.eval` above in structure, but instead of evaluating
for the final result, it recursively decompose the safety proof obligation into
obligations of smaller components that are fulfiled independently and incrementally. The compile-time
`Compiler.Env.forSemantic` F-bound bridge can be used to save/load proven goal; this
is separate from runtime value binding and never calls `eval`.

Malformed or incompatible component will immediate cause the compilation to
fail. In particular, applications must compile both sides successfully, the function side
must satisfy `.fn` or `.primitiveFn` precondition, and the argument must be compatible with the
function input.

On success, it preserves the source
program shape: values remain values, references remain references, and
applications remain applications of recursively compiled subterms.

Fuel `0` returns `.outOfFuel`; every recursive descent consumes fuel.
-/
def compile (trm : Trm I) (desired: Condition I)
: RecOption (Program desired)
  | 0 => .outOfFuel
  | _fuel + 1 =>
    match trm with
    | typeHinted self _ => self.compile desired _fuel
    | .val value => sorry
    | .apply _fn _arg => sorry
    | .ref _i => .yield none


def compileToTrm (trm : Trm I)
  (condition: Condition I := fun _ => true)-- by default, accept any condition
: RecOption (Trm I) := fun (fuel : Nat) =>
  (trm.compile condition fuel).map (fun out => out.map (fun v => v.trm))

end AST.Trm

end

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

end

end DTLC

end Lp2lc.Active
