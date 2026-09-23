import Std
import «Lp2lc».Active.Util

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

mutual

/-- Function-valued syntax for one lambda body over the reference carrier. -/
inductive Binder : Parameters → Label → Type 2 where
| mk (body : P.C -> AST P l) : Binder P l -- with built-in domain expansion?


/-- Source type syntax.

`TLit` classifies primitive bytecode values and `TFn` classifies functions.
-/
inductive AST : Parameters → Label → Type 2 where
/- Values are successful evaluation results and atomic application arguments. -/
| TLit : AST P .typ -- `AnyVal` in Scala, accepts only primitive values
| lit (repr : P.B) : AST P .val -- most specific type is always `primitive`

/- Function bodies receive the reference value supplied when the function runs. -/
| TFn (tIn : AST P .typ) (tOut : AST P .typ) : AST P .typ -- function
| fn (tIn : AST P .typ) (body : Binder P .trm) : AST P .val -- most specific type is always `.fn tIn _`
/-- Terms contain values, applications, or references. -/

| val (v : AST P .val) : AST P .trm -- AKA literal
| apply (fn : AST P .trm) (arg : AST P .trm) : AST P .trm -- fn must be a function that can be applied on arg
| ref (receipt : P.C) : AST P .trm -- reference, AKA variable/var (I don't like this name as it implies mutability in Scala)
end

namespace Binder
-- All theorems about Binder should be here, e.g. parametricity, lift relation

/-- Replaces the newest structural lambda slot while preserving outer binders. -/
def apply {P : Parameters} {l : Label}
    (self : Binder P l) (arg : P.C) : AST P l :=
  match self with
  | .mk body =>
    body arg

end Binder

section variable {P : Parameters}

class Labelled (Ctor : Label → Type 2)

namespace Labelled -- TODO: this should contains shared abbrev for both AST and Src_, but we don't know how to do this
section variable {Ctor} (this: Labelled Ctor)

abbrev Typ := Ctor .typ
abbrev Trm := Ctor .trm
abbrev Val := Ctor .val

end
end Labelled

namespace AST

abbrev Typ (P : Parameters) := AST P .typ
abbrev Trm (P : Parameters) := AST P .trm
abbrev Val (P : Parameters) := AST P .val

section variable (P : Parameters)

end

namespace Val

def asTrm (self : AST.Val P) : AST.Trm P := .val self

end Val

end AST

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE : LE (AST.Typ P) := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
@[instance_reducible]
instance typDecidableLE : DecidableLE (AST.Typ P)
  | .TLit, .TLit => isTrue rfl
  | .TLit, .TFn _ _
  | .TFn _ _, .TLit => isFalse (λ equality => nomatch equality)
  | .TFn leftIn leftOut, .TFn rightIn rightOut =>
    match typDecidableLE leftIn rightIn, typDecidableLE leftOut rightOut with
    | isTrue inputEqual, isTrue outputEqual => isTrue (inputEqual ▸ outputEqual ▸ rfl)
    | isFalse notEqual, _ => isFalse (λ equality => notEqual (AST.TFn.inj equality).1)
    | _, isFalse notEqual => isFalse (λ equality => notEqual (AST.TFn.inj equality).2)

end

/--
Shares one receipt carrier between executable values and build-time types.

The underlying view stores a tagged value-or-type payload. Runtime and build
contexts expose independently typed [KVRefs.Lesser] views over the same receipt
carrier. Their equivalences mint receipts only from the matching payload, while
[Binder] distinguishes bound slots structurally so lambda construction cannot
inspect phase-specific minted receipts.
-/

class HasUId2Any extends HasByteCode, HasUId where
  uid2any : KVRefs UId (
    let P : Parameters := { C := UId, B := B }

    AST.Val P ⊕ AST.Typ P
  )

namespace HasUId2Any
section variable (this : HasUId2Any)

/-- The shared syntax parameters are fixed by the mixed receipt view. -/
abbrev Parameters : Parameters := { C := this.UId, B := this.B }

end
end HasUId2Any

/-- Owns the runtime receipt bridge for executable STLC values. -/
class ExeEnv (refs : HasUId2Any) where
  uid2val : refs.uid2any.Lesser refs.UId (AST.Val refs.Parameters)
  uid2valCtx : KVEquiv uid2val.toKVRefs

namespace AST

/-- Evaluates executable terms whose references carry receipts from the runtime context. -/
def eval {refs} [exe : ExeEnv refs]
    (self : Trm refs.Parameters) : RecOpt (Val refs.Parameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      let anf := (eval fnTerm fuel, eval arg fuel)
      match anf with
      | (.yield (some (fn _tIn body)), .yield (some arg)) =>
        let receipt := exe.uid2valCtx.inv arg
        eval (body.apply receipt) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref receipt => .yield (some (exe.uid2val.get receipt))

end AST

end Lp2lc.Active.STLC
