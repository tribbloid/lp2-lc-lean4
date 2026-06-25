import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace STLC

/- Shared STLC syntax family, currently exposing function types over the common representation. -/
open Lp2lc.Active.Util

section variable {I : Free}

namespace AST
section variable (I : Free)

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

Primitive value terms are self-typed, while function values carry their input
type. Applications and references are unannotated.

In HOAS there is no syntax-level context binding terms to types, so function
input annotations are the extrinsic typing evidence available to the compiler.
They are not intrinsic typing indices on terms.
-/

inductive Trm : Type where
| val (v : Val) -- AKA literal
| apply (fn : Trm) (arg : Trm) -- fn must be a function that can be applied on arg
| ref (s: I.Index) -- binded reference, AKA variable/var (I don't like this name as it implies mutability in Scala)


/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Function values carry their input type so the compiler can type-check HOAS bodies.
-/
inductive Val : Type where
| primitive (repr : I.Data) -- most specific type is always `primitive`
| fn (body : (arg : I.Index) → Trm) (tIn : Typ) -- most specific type is always `.fn tIn _`

end
end
end AST

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE : LE (AST.Typ I) := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
instance typDecidableLE : DecidableLE (AST.Typ I)
  | .primitive, .primitive => isTrue rfl
  | .primitive, .fn _ _
  | .fn _ _, .primitive => isFalse (fun equality => nomatch equality)
  | .fn leftIn leftOut, .fn rightIn rightOut =>
    match typDecidableLE leftIn rightIn, typDecidableLE leftOut rightOut with
    | isTrue inputEqual, isTrue outputEqual => isTrue (inputEqual ▸ outputEqual ▸ rfl)
    | isFalse notEqual, _ => isFalse (fun equality => notEqual (AST.Typ.fn.inj equality).1)
    | _, isFalse notEqual => isFalse (fun equality => notEqual (AST.Typ.fn.inj equality).2)

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

abbrev Condition (I : Free) := (value : AST.Val I) -> Prop -- AKA semantic type. TODO: this should be made irrelevant to I being chosen.

namespace AST.Trm
section variable [env: @Runtime.Env I]

/--
Evaluates a term by spending 1 fuel at each semantic
descent. Runtime evaluation uses `FBound I Val` for references and deliberately
does not inspect compile-time typing evidence.
-/
def eval (self : AST.Trm I) : RecOption (AST.Val I)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fn arg =>
      let anf := (fn.eval fuel, arg.eval fuel) -- ANF, atomic normal form
      match anf with
      | (.yield (some (.fn body _tIn)), .yield (some input)) =>
        let permission := env.canEvalAny input
        let index := env.valueRefs.save (p := ()) ⟨input, permission⟩
        (body index).eval fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref i =>
      .yield (some (env.valueRefs.load (p := ()) i).1)

end

def RecCanInhabit_semantic (self : AST.Trm I) (condition : Condition I) : ∀ [@Runtime.Env I], Rec Prop := fun fuel =>
  (self.eval fuel).map (fun
    | some v => condition v
    | none => False)

/--
An safe term may run out of runtime fuel, but it must not reach runtime
`error`. When a runtime value is produced, it must satisfy the condition.
-/
def CanInhabit_semantic (term : AST.Trm I) (condition : Condition I) : Prop :=
  ∀ fuel, ∀ [@Runtime.Env I], match term.RecCanInhabit_semantic condition fuel with
  | .yield proposition => proposition
  | .outOfFuel => True

/-- Converts semantic outcomes into obligations over all fuel and runtime environments. -/
abbrev WeakestPre := @CanInhabit_semantic I -- weakest precondition in Iris framework

def IsSafe (self : AST.Trm I) : Prop :=
  self.CanInhabit_semantic (fun _ => true)

end AST.Trm

-- namespace Internal

-- /--
-- a compiled term with safety proof
-- -/
-- private structure _AdequateTrm (condition : Condition I) where
--   trm: AST.Trm I
--   safetyEv: trm.IsSafeBy condition

-- end Internal

-- abbrev AdequateTrm := @Internal._AdequateTrm I

-- namespace AdequateTrm
-- section variable {c: Condition I} (self: AdequateTrm c) [env : @Runtime.Env I]

-- def eval : MaySucceed ({v : AST.Val I // c v}) := fun fuel =>
--   match h : self.trm.eval fuel with
--   | .result value =>
--     ⟨.result ⟨value, by
--       have evidence := self.safetyEv fuel
--       simpa [h] using evidence⟩, by
--         simp [Outcome.isResultOrOutOfFuel]⟩
--   | .error =>
--     have noError := self.safetyEv fuel
--     False.elim (by
--       simp [h] at noError)
--   | .outOfFuel =>
--     ⟨.outOfFuel, by
--       simp [Outcome.isResultOrOutOfFuel]⟩

-- end
-- end AdequateTrm

namespace Compiler

/--
Contains compile-time FBound bridges for semantic obligations.
-/
class Env (I : Free) : Type where
  -- trmRefs : @DepFBound (Condition I) (Condition.DepIndex) (AdequateTrm)
  typRefs : FBound I.Index (AST.Typ I)
  -- TODO: revise this trmRefs if necessary

end Compiler

section variable [env: @Compiler.Env I]
open AST

namespace AST.Trm
section variable (self: Trm I)

/--
get the strongest post type bound (post-condition) of a term, or throw an error
-/
def infer (trm : Trm I) : RecOption (Typ I)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val (.primitive _repr) => .yield (some .primitive)
    | .val (.fn body tIn) =>
      let index := env.typRefs.save (p := ()) tIn
      ((body index).infer fuel).map (fun out => out.map (fun tOut => .fn tIn tOut))
    | .apply fn arg =>
      match fn.infer fuel, arg.infer fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | .ref i => .yield (some (env.typRefs.load (p := ()) i))


def RecCanInhabit (self : Trm I) (typ : Typ I) : Rec Prop := sorry -- AKA compile, this serve as the prior condition of the Fundamental theorem

/--
determine if a term can can inhabit a type bound.

Structurally it should be similar to infer, but return a Prop/proof obligation instead of a precise type bound
-/
def CanInhabit (self : Trm I) (typ : Typ I) : Prop :=
  ∀ fuel, match term.RecCanInhabit typ fuel with
  | .yield proposition => proposition
  | .outOfFuel => True

end
end AST.Trm

/-- Interprets source types as semantic conditions over values. -/
def AST.Typ.ToCondition (typ: Typ I): Condition I := fun value =>
  let trm := Trm.val value
  (trm.CanInhabit typ)

/-- States that syntactic typing entails semantic typing by the interpreted type. -/
def Fundamental : Prop :=
  ∀ (term : Trm I) (type : Typ I),
    term.CanInhabit type → term.WeakestPre (type.ToCondition)

-- def _proofFundamental (term : Trm I) (type : Typ I) : term.CanInhabit type → term.CanInhabit_semantic (type.ToCondition) := sorry
  -- | 0 => .outOfFuel
  -- | fuel + 1 =>
  --   match trm with
  --   | .val (.primitive _repr) => .result .primitive
  --   | .val (.fn body tIn) =>
  --     let index := env.typRefs.save (p := ()) tIn
  --     match (body index).infer fuel with
  --     | .result tOut => .result (.fn tIn tOut)
  --     | .error => .error
  --     | .outOfFuel => .outOfFuel
  --   | .apply fn arg =>
  --     match fn.infer fuel, arg.infer fuel with
  --     | .result (.fn tIn tOut), .result argTyp =>
  --       if argTyp ≤ tIn then .result tOut else .error
  --     | .outOfFuel, _ => .outOfFuel
  --     | _, .outOfFuel => .outOfFuel
  --     | _, _ => .error
  --   | .ref i => .result (env.typRefs.load (p := ()) i)


end

/-- States that semantic typing of a closed term entails operational safety. -/
def Adequacy : Prop :=
  ∀ (term : AST.Trm I) (postcondition : Condition I),
    term.WeakestPre postcondition → term.IsSafe

end

end STLC

end Lp2lc.Active
