import Std
import «Lp2lc».Active.Util

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

mutual

/-- Source type syntax.

`primitive` classifies primitive bytecode values and `fn` classifies functions.
-/
inductive AST : Parameters → Label → Type 2 where
| primitive : AST P .typ -- `AnyVal` in Scala, accepts only primitive values
| fn (tIn : AST P .typ) (tOut : AST P .typ) : AST P .typ -- function
/--
Source term syntax.

Primitive value terms are self-typed, while function values carry their input
type. Applications and references are unannotated.

In HOAS there is no syntax-level context binding terms to types, so function
input annotations are the extrinsic typing evidence available to the compiler.
They are not intrinsic typing indices on terms.
-/
| val (v : AST P .val) : AST P .trm -- AKA literal
| apply (fn : AST P .trm) (arg : AST P .trm) : AST P .trm -- fn must be a function that can be applied on arg
| ref (receipt : P.C) : AST P .trm -- reference, AKA variable/var (I don't like this name as it implies mutability in Scala)
/--
Value syntax, containing neither references nor applications.

Values are the successful result of evaluation and the atomic argument form
used by function application after both sides have been evaluated.

Function values carry their input type so the compiler can type-check structural bodies.
-/
| lit (repr : P.D) : AST P .val -- most specific type is always `primitive`
/--
Binds one fresh structural reference after the outer [P.C] carrier.

The body stores first-order syntax whose newest reference is represented by
the right summand. Evaluation and inference replace that slot with their own
minted receipt, so lambda construction cannot inspect those receipts.
-/
| lam (body : Binder P .trm)
    (tIn : AST P .typ) : AST P .val -- most specific type is always `.fn tIn _`

/-- First-order syntax with one distinguished newest reference slot. -/
inductive Binder : Parameters → Label → Type 2 where
| mk (body : AST { P with C := P.C ⊕ Unit } l) : Binder P l

end

mutual

/-
TODO:
very long "recarrier" will muddle the proof.

In theory, it's fine for an AST with more general carrier to contain AST with more specific carrier

namely: it's fine for `AST P1 x` to contain `AST P2 y` as subnode, if `P2.C <:< P1.C` (with an upcast embedding)

if this is authentically reflected in AST design, both recarrier function can be deleted, and partially-reduced AST can be used in inference directly

This is a conjecture revision task, keep your change local, minimal & don't repeat yourself
-/
  /-- Rebuilds syntax after mapping its reference and data carriers. -/
  @[simp]
  def AST.recarrier {P Q : Parameters} {l : Label} (self : AST P l)
      (mapC : P.C → Q.C) (mapD : P.D → Q.D) : AST Q l :=
    match self with
    | .primitive => .primitive
    | .fn tIn tOut =>
      .fn (tIn.recarrier mapC mapD) (tOut.recarrier mapC mapD)
    | .val value => .val (value.recarrier mapC mapD)
    | .apply fnTerm arg =>
      .apply (fnTerm.recarrier mapC mapD) (arg.recarrier mapC mapD)
    | .ref receipt => .ref (mapC receipt)
    | .lit repr => .lit (mapD repr)
    | .lam body tIn =>
      .lam (body.recarrier mapC mapD) (tIn.recarrier mapC mapD)

  /-- Maps the outer carriers of a binder while preserving its newest slot. -/
  @[simp]
  def Binder.recarrier {P Q : Parameters} {l : Label} (self : Binder P l)
      (mapC : P.C → Q.C) (mapD : P.D → Q.D) : Binder Q l :=
    match self with
    | .mk body =>
      .mk (body.recarrier
        (λ receipt =>
          match receipt with
          | .inl outer => .inl (mapC outer)
          | .inr () => .inr ())
        mapD)

end

namespace Binder
-- All theorems about Binder should be here, e.g. parametricity, lift relation

/-- Replaces the newest structural lambda slot while preserving outer binders. -/
def apply {P : Parameters} {l : Label}
    (self : Binder P l) (arg : P.C) : AST P l :=
  match self with
  | .mk body =>
    body.recarrier
      (λ receipt =>
        match receipt with
        | .inl outer => outer
        | .inr () => arg)
      id

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

open AST -- FIXME: get rid of this, all AST should be at the beginning of the file

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE : LE (AST.Typ P) := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
@[instance_reducible]
instance typDecidableLE : DecidableLE (AST.Typ P)
  | .primitive, .primitive => isTrue rfl
  | .primitive, .fn _ _
  | .fn _ _, .primitive => isFalse (λ equality => nomatch equality)
  | .fn leftIn leftOut, .fn rightIn rightOut =>
    match typDecidableLE leftIn rightIn, typDecidableLE leftOut rightOut with
    | isTrue inputEqual, isTrue outputEqual => isTrue (inputEqual ▸ outputEqual ▸ rfl)
    | isFalse notEqual, _ => isFalse (λ equality => notEqual (AST.fn.inj equality).1)
    | _, isFalse notEqual => isFalse (λ equality => notEqual (AST.fn.inj equality).2)

end

/--
Shares one receipt carrier between executable values and build-time types.

The underlying view stores a tagged value-or-type payload. Runtime and build
contexts refine that view independently through [KVEquiv.Lesser]. The subtype
proof certifies which payload is available, while [Binder] distinguishes bound
slots structurally so lambda construction cannot inspect phase-specific minted
receipts.
-/

class HasUId2Any extends HasData, HasUId where
  uid2any : KVRefs UId (
    let P : Parameters := { C := UId, D := D }

    AST.Val P ⊕ AST.Typ P
  )

namespace HasUId2Any
section variable (this : HasUId2Any)

/-- The shared syntax parameters are fixed by the mixed receipt view. -/
abbrev Parameters : Parameters := { C := this.UId, D := this.D }

end
end HasUId2Any

/-- Owns the runtime receipt bridge for executable STLC values. -/
class ExeEnv (refs : HasUId2Any) extends KVRefs.HasEv refs.UId where
  uid2val : refs.uid2any.Lesser {x // ev x} (AST.Val {refs.Parameters with C := {x // ev x}})
  uid2valCtx : KVEquiv uid2val.toKVRefs

namespace ExeEnv
section variable {refs} (this: ExeEnv refs)

abbrev Parameters : Parameters := {refs.Parameters with C := {x // this.ev x}}

end
end ExeEnv

namespace AST

/-- Evaluates executable terms whose references carry receipts from the runtime context. -/
def eval {refs} [exe : ExeEnv refs]
    (self : Trm (ExeEnv.Parameters exe)) : RecOpt (Val (ExeEnv.Parameters exe))
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      let anf := (eval fnTerm fuel, eval arg fuel)
      match anf with
      | (.yield (some (.lam body _tIn)), .yield (some arg)) =>
        let receipt := exe.uid2valCtx.inv arg
        eval (body.apply receipt) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref receipt => .yield (some (exe.uid2val.get receipt))

end AST

end Lp2lc.Active.STLC
