import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace STLC

/- Shared STLC syntax family, currently exposing function types over the common representation. -/
open Lp2lc.Active.Util

section variable {I : Impl}

namespace AST
section variable (I : Impl)

mutual

/--
Source type syntax.

`primitive` classifies primitive bytecode values and `fn` classifies functions.
-/
inductive Typ : Type where
| primitive -- `AnyVal` in Scala, accepts only primitive values
| fn (tIn : Typ) (tOut : Typ) -- function

/--
Source term syntax.

Every value term carries a mandatory type annotation. Applications and
references are unannotated. Annotations are compile-time constraints only:
compilation checks them and runtime evaluation ignores them.

In HOAS there is no syntax-level context binding terms to types, so value
annotations are the extrinsic typing evidence available to the compiler. They
are not intrinsic typing indices on terms.
-/

-- TODO: this definition has 2 problems: can eval at compiletime, cannot express
-- primitive fn that modify bytecode
inductive Trm : Type where
| val (v : Val) (hint : Typ) -- AKA literal
| apply (fn : Trm) (arg : Trm) -- fn must be a function that can be applied on arg
| ref (s: I.Index) -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala)


/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Value represents both runtime and compiletime data, it should nevery carry type information due to type erasure
-/
inductive Val : Type where
| primitive (repr : I.Data) -- most specific type is always `primitive`
| fn (body : (arg : I.Index) → Trm) -- most specific type is always `.fn _ _`

end

end

namespace Trm

structure TypeView where (self: Trm I)

def typeHint (self: Trm I) := TypeView.mk self

namespace TypeView

/-- Reads the mandatory annotation attached to an outer value term. -/
def get (view : @TypeView I) : Option (Typ I) :=
  match view.self with
  | .val _ hint => some hint
  | _ => none

end TypeView

end Trm

end AST

namespace AST.Val

end AST.Val

namespace Runtime
class Env where
  CanSave : Permission (AST.Val I)
  -- valueRefGen {TP: Type} : DepFBound (TP -> I.Index) (TP -> { value : AST.Val I // CanSave value }) -- TODO: don't know how to define this prior
  valueRefs: FBound I.Index { value : AST.Val I // CanSave value }
  canEvalAny: (v: AST.Val I) -> CanSave v
  -- fuel: Nat -- this can't be used, ewww

end Runtime

abbrev Condition (I : Impl) := (value : AST.Val I) -> Prop -- AKA semantic type. TODO: this should be made irrelevant to I being chosen.

namespace AST.Trm
section variable (self : AST.Trm I) [env: @Runtime.Env I]

/--
Evaluates a term by spending 1 fuel at each semantic
descent. Runtime evaluation uses `FBound I Val` for references and deliberately
does not inspect compile-time typing evidence.
-/
def eval (self : AST.Trm I) : MayTerminate (AST.Val I) -- TODO: circumventing https://github.com/leanprover/lean4/issues/14061
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value _hint => .result value
    | .apply fn arg =>
      let anf := (fn.eval fuel, arg.eval fuel) -- ANF, atomic normal form
      match anf with
      | (.result (.fn body), .result input) =>
        let permission := env.canEvalAny input
        let index := env.valueRefs.save (p := ()) ⟨input, permission⟩
        (body index).eval fuel
      | (.outOfFuel, _) | (_, .outOfFuel) => .outOfFuel
      | _ => .error
    | .ref i =>
      .result (env.valueRefs.load (p := ()) i).1

end

/--
An safe term may run out of runtime fuel, but it must not reach runtime
`error`. When a runtime value is produced, it must satisfy the condition.
-/
def IsSafeBy (self : AST.Trm I) (condition : Condition I) : Prop :=
  ∀ (fuel : Nat) [@Runtime.Env I], match self.eval fuel with
  | .result value => condition value
  | .error => false
  | .outOfFuel => true

def IsSafe (self : AST.Trm I) : Prop :=
  IsSafeBy self (fun _ => true)

-- def IsSafeUnder (self : AST.Trm I) (condition : Condition I) : Prop :=

end AST.Trm

namespace Internal

/--
a compiled term with safety proof
-/
private structure _AdequateTrm (condition : Condition I) where
  trm: AST.Trm I
  safetyEv: trm.IsSafeBy condition

end Internal

abbrev AdequateTrm := @Internal._AdequateTrm I

namespace AdequateTrm
section variable {c: Condition I} (self: AdequateTrm c) [env : @Runtime.Env I]

def eval : MaySucceed ({v : AST.Val I // c v}) := fun fuel =>
  match h : self.trm.eval fuel with
  | .result value =>
    ⟨.result ⟨value, by
      have evidence := self.safetyEv fuel
      simpa [h] using evidence⟩, by
        simp [Outcome.isResultOrOutOfFuel]⟩
  | .error =>
    have noError := self.safetyEv fuel
    False.elim (by
      simp [h] at noError)
  | .outOfFuel =>
    ⟨.outOfFuel, by
      simp [Outcome.isResultOrOutOfFuel]⟩

end
end AdequateTrm

namespace Compiler

namespace Condition

structure DepIndex (self: Condition I) where
  index: I.Index

end Condition

/--
Contains compile-time FBound bridges for semantic obligations.
-/
class Env (I : Impl) : Type where
  trmRefs : @DepFBound (Condition I) (Condition.DepIndex) (AdequateTrm)
  typRefs : FBound I.Index (AST.Typ I)
  -- TODO: revise this trmRefs if necessary

end Compiler

section variable [env: @Compiler.Env I]
open AST

def WeakestPre : Type := Typ I

namespace AST.Trm

/--
similar to Trm.compile, but only produce the safety proof
-/
def infer (trm : Trm I) : MayTerminate (Typ I)
  | 0 => .outOfFuel
  | _fuel + 1 =>
    match trm with
    | .val value hint => sorry
    | .apply _fn _arg => sorry
    | .ref _i => .error

/--
Fuel-guarded compiler API for recursively type-checking `Trm` syntax,

- if valid return an `AdequateTrm` with safety proof.
- if malformed return error

it does not evaluate the program.

It's very similar to `Trm.eval` above in structure, but instead of evaluating
for the final result, it recursively decompose the safety proof obligation into
obligations of smaller components that are fulfiled independently and incrementally. The F-bound bridge in
`Compiler.Env` can be used to save/load proven goal; this
is separate from runtime value binding and never calls `eval`.

Malformed term will cause the compilation to
fail. In particular, applications must compile both sides successfully, the function side
must satisfy the `.fn` precondition, and the argument must be compatible with the
function input.

On success, it preserves the source
program shape: values remain values, references remain references, and
applications remain applications of recursively compiled subterms.

Fuel `0` returns `.outOfFuel`; every recursive descent consumes fuel.
-/
def compile (trm : Trm I) (c : Condition I)
: MayTerminate (AdequateTrm c)
  | 0 => .outOfFuel
  | _fuel + 1 =>
    match trm with
    | .val _value hint =>
      let extraC : Condition I := sorry --TODO: this is the semantic counterpart of hint
      sorry
    | .apply _fn _arg => sorry
    | .ref _i => sorry

end AST.Trm

end

end

end STLC

end Lp2lc.Active
