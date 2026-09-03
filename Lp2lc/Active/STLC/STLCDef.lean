import Std
import «Lp2lc».Active.Util

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

private inductive RawAST : Parameters → Label → Type 2 where
| primitive : RawAST P .typ
| fn (tIn : RawAST P .typ) (tOut : RawAST P .typ) : RawAST P .typ
| val (value : RawAST P .val) : RawAST P .trm
| apply (fnTerm : RawAST P .trm) (arg : RawAST P .trm) : RawAST P .trm
| ref (receipt : P.C) (tIn : RawAST P .typ) : RawAST P .trm
| capture (value : RawAST P .val) : RawAST P .trm
| lit (repr : P.D) : RawAST P .val
| lam (body : P.C → RawAST P .trm)
    (tIn : RawAST P .typ) (tOut : RawAST P .typ) : RawAST P .val

private inductive RawValHasType {P : Parameters} :
    RawAST P .val → RawAST P .typ → Prop where
| lit (repr : P.D) : RawValHasType (.lit repr) .primitive
| lam (body : P.C → RawAST P .trm)
    (tIn : RawAST P .typ) (tOut : RawAST P .typ) :
    RawValHasType (.lam body tIn tOut) (.fn tIn tOut)

private inductive RawHasType {P : Parameters} :
    RawAST P .trm → RawAST P .typ → Prop where
| val (typed : RawValHasType value typ) : RawHasType (.val value) typ
| apply (fnTyped : RawHasType fnTerm (.fn tIn tOut))
    (argTyped : RawHasType arg tIn) : RawHasType (.apply fnTerm arg) tOut
| ref (receipt : P.C) (tIn : RawAST P .typ) : RawHasType (.ref receipt tIn) tIn
| capture (typed : RawValHasType value typ) : RawHasType (.capture value) typ

private inductive RawCertified {P : Parameters} :
    {label : Label} → RawAST P label → Prop where
| primitive : RawCertified .primitive
| fn (input : RawCertified tIn) (output : RawCertified tOut) :
    RawCertified (.fn tIn tOut)
| val (value : RawCertified rawValue) : RawCertified (.val rawValue)
| apply (fnTerm : RawCertified rawFn) (arg : RawCertified rawArg) :
    RawCertified (.apply rawFn rawArg)
| ref (receipt : P.C) (input : RawCertified tIn) :
    RawCertified (.ref receipt tIn)
| capture (value : RawCertified rawValue) : RawCertified (.capture rawValue)
| lit (repr : P.D) : RawCertified (.lit repr)
| lam (input : RawCertified tIn) (output : RawCertified tOut)
    (body : ∀ (arg : P.C), RawCertified (rawBody arg))
    (typed : ∀ (arg : P.C), RawHasType (rawBody arg) tOut) :
    RawCertified (.lam rawBody tIn tOut)

/-- Source syntax whose recursive certificate is inaccessible to unchecked construction. -/
structure AST (P : Parameters) (label : Label) : Type 2 where
  private mk ::
  private raw : RawAST P label
  private certified : RawCertified raw

/-- Source type syntax.

`primitive` classifies primitive bytecode values and `fn` classifies functions.
-/
/-
FIXME: Switch to certified AST

The representation revision is present: lambda bodies now carry one fixed output
type and certificates for typing and executable bindings. Bound receipts are
opaque, while captured values use an explicit node and never become raw receipts.
Evaluation and inference inspect only [AST.View].

The dependent soundness, monotonicity, and Umbral proof discharge remains pending.
De Bruijn serials and explicit substitution/recarrier operations remain excluded.
-/

section variable {P : Parameters}

namespace AST

abbrev Typ (P : Parameters) := AST P .typ
abbrev Trm (P : Parameters) := AST P .trm
abbrev Val (P : Parameters) := AST P .val

section variable (P : Parameters)

end

def primitive : AST P .typ := ⟨.primitive, .primitive⟩

def fn (tIn : AST P .typ) (tOut : AST P .typ) : AST P .typ :=
  ⟨.fn tIn.raw tOut.raw, .fn tIn.certified tOut.certified⟩

/-- Source term containing a value. -/
def val (value : AST P .val) : AST P .trm :=
  ⟨.val value.raw, .val value.certified⟩

/-- Untyped application; inference remains responsible for rejecting mismatched operands. -/
def apply (fnTerm : AST P .trm) (arg : AST P .trm) : AST P .trm :=
  ⟨.apply fnTerm.raw arg.raw, .apply fnTerm.certified arg.certified⟩

/-- Embeds a certified captured value without manufacturing a reference receipt. -/
def capture (value : AST P .val) : AST P .trm :=
  ⟨.capture value.raw, .capture value.certified⟩

def lit (repr : P.D) : AST P .val := ⟨.lit repr, .lit repr⟩

/-- The intrinsic typing certificate carried by a term. -/
def HasType (self : AST.Trm P) (typ : AST.Typ P) : Prop :=
  RawHasType self.raw typ.raw

/-- Evidence that every reference in a term originates from a lambda binding. -/
def HasExecutableBindings (self : AST P label) : Prop :=
  RawCertified self.raw

/-- A term paired with its fixed source type. -/
structure Typed (typ : AST.Typ P) where
  private mk ::
  trm : AST.Trm P
  private typed : trm.HasType typ

/-- An opaque lambda argument; its receipt can only be consumed by [AST.ref]. -/
structure Bound (tIn : AST.Typ P) where
  private mk ::
  private receipt : P.C

/-- Constructs a reference only from a lambda-bound argument. -/
def ref {tIn : AST.Typ P} (self : Bound tIn) : AST.Trm P :=
  ⟨.ref self.receipt tIn.raw, .ref self.receipt tIn.certified⟩

namespace Bound

/-- Recovers the input typing certificate attached to a bound argument. -/
def asTyped {tIn : AST.Typ P} (self : Bound tIn) : Typed tIn :=
  ⟨self.ref, .ref self.receipt tIn.raw⟩

end Bound

/--
A PHOAS callback with one output type, its typing certificate, and executable
binding evidence. The public constructor supplies an opaque bound argument, so
the callback cannot inspect phase-specific receipt identity.
-/
structure LamBody (tIn tOut : AST.Typ P) where
  private intro ::
  body : P.C → AST.Trm P
  typed : ∀ (arg : P.C), (body arg).HasType tOut
  executable : ∀ (arg : P.C), (body arg).HasExecutableBindings

namespace LamBody

/-- Builds a certified body by erasing only the opaque argument wrapper. -/
def mk {tIn tOut : AST.Typ P} (body : Bound tIn → Typed tOut) :
    LamBody tIn tOut :=
  .intro
    (λ arg => (body ⟨arg⟩).trm)
    (λ arg => (body ⟨arg⟩).typed)
    (λ arg => (body ⟨arg⟩).trm.certified)

end LamBody

/-- Constructs a function value only from a fixed-output certified body. -/
def lam {tIn tOut : AST.Typ P} (body : LamBody tIn tOut) : AST.Val P :=
  ⟨.lam (λ arg => (body.body arg).raw) tIn.raw tOut.raw,
    .lam tIn.certified tOut.certified
      (λ arg => body.executable arg) (λ arg => body.typed arg)⟩

namespace Typed

/-- Builds a typed application while [AST.apply] itself remains untyped. -/
def apply {tIn tOut : AST.Typ P} (fnTerm : Typed (.fn tIn tOut))
    (arg : Typed tIn) : Typed tOut :=
  ⟨AST.apply fnTerm.trm arg.trm, .apply fnTerm.typed arg.typed⟩

end Typed

-- TOOD: remove & don't use it, we don't need general upcast for AST.
-- def map {B : UIdU} {PF QF : UIdU} {PD QD : DataU} {l : Label}
--     (self : AST { F := PF, B := B, D := PD } l)
--     (mF : PF → QF) (mD : PD → QD) :
--     AST { F := QF, B := B, D := QD } l :=
--   match self with
--   | .primitive => .primitive
--   | .fn tIn tOut => .fn (tIn.map mF mD) (tOut.map mF mD)
--   | .val v => .val (v.map mF mD)
--   | .apply fnTerm arg => .apply (fnTerm.map mF mD) (arg.map mF mD)
--   | .ref (.inl f) => .ref (.inl (mF f))
--   | .ref (.inr b) => .ref (.inr b)
--   | .lit repr => .lit (mD repr)
--   | .lam body tIn => .lam (λ arg => (body arg).map mF mD) (tIn.map mF mD)

namespace Val

def asTrm (self : AST.Val P) : AST.Trm P := .val self

/-- Computes the type already certified by a value constructor. -/
def typ (self : AST.Val P) : AST.Typ P :=
  match self with
  | ⟨.lit _, .lit _⟩ => .primitive
  | ⟨.lam _ tIn tOut, .lam input output _ _⟩ =>
    ⟨.fn tIn tOut, .fn input output⟩

/-- Views a value term together with its constructor-determined type. -/
def asTyped (self : AST.Val P) : Typed self.typ :=
  match self with
  | ⟨.lit repr, .lit _⟩ => ⟨self.asTrm, .val (.lit repr)⟩
  | ⟨.lam body tIn tOut, .lam _ _ _ _⟩ =>
    ⟨self.asTrm, .val (.lam body tIn tOut)⟩

/-- Views a captured value term together with its constructor-determined type. -/
def asCaptured (self : AST.Val P) : Typed self.typ :=
  match self with
  | ⟨.lit repr, .lit _⟩ => ⟨AST.capture self, .capture (.lit repr)⟩
  | ⟨.lam body tIn tOut, .lam _ _ _ _⟩ =>
    ⟨AST.capture self, .capture (.lam body tIn tOut)⟩

end Val

/-- One certified layer exposed without an unchecked constructor or raw projection. -/
inductive View (P : Parameters) : Label → Type 2 where
| primitive : View P .typ
| fn (tIn : AST.Typ P) (tOut : AST.Typ P) : View P .typ
| val (value : AST.Val P) : View P .trm
| apply (fnTerm : AST.Trm P) (arg : AST.Trm P) : View P .trm
| ref (receipt : P.C) (tIn : AST.Typ P) : View P .trm
| capture (value : AST.Val P) : View P .trm
| lit (repr : P.D) : View P .val
| lam (tIn : AST.Typ P) (tOut : AST.Typ P)
    (body : LamBody tIn tOut) : View P .val

/-- Exposes one certified AST layer while retaining all recursive certificates. -/
def view {label : Label} (self : AST P label) : View P label :=
  match self with
  | ⟨.primitive, .primitive⟩ => .primitive
  | ⟨.fn tIn tOut, .fn input output⟩ =>
    .fn ⟨tIn, input⟩ ⟨tOut, output⟩
  | ⟨.val value, .val certified⟩ => .val ⟨value, certified⟩
  | ⟨.apply fnTerm arg, .apply fnCertified argCertified⟩ =>
    .apply ⟨fnTerm, fnCertified⟩ ⟨arg, argCertified⟩
  | ⟨.ref receipt tIn, .ref _ input⟩ => .ref receipt ⟨tIn, input⟩
  | ⟨.capture value, .capture certified⟩ => .capture ⟨value, certified⟩
  | ⟨.lit repr, .lit _⟩ => .lit repr
  | ⟨.lam rawBody tIn tOut, .lam input output body typed⟩ =>
    let tInAst : AST.Typ P := ⟨tIn, input⟩
    let tOutAst : AST.Typ P := ⟨tOut, output⟩
    .lam tInAst tOutAst
      (.intro (λ arg => ⟨rawBody arg, body arg⟩)
        (λ arg => typed arg) (λ arg => body arg))

private theorem extRaw {left right : AST P label}
    (raw : left.raw = right.raw) : left = right := by
  cases left
  cases right
  cases raw
  rfl

private def rawTypDecidableEq (left right : RawAST P .typ) :
    Decidable (left = right) :=
  match left, right with
  | .primitive, .primitive => isTrue rfl
  | .primitive, .fn _ _
  | .fn _ _, .primitive => isFalse (λ equality => nomatch equality)
  | .fn leftIn leftOut, .fn rightIn rightOut =>
    match rawTypDecidableEq leftIn rightIn, rawTypDecidableEq leftOut rightOut with
    | isTrue inputEqual, isTrue outputEqual =>
      isTrue (inputEqual ▸ outputEqual ▸ rfl)
    | isFalse notEqual, _ =>
      isFalse (λ equality => notEqual (RawAST.fn.inj equality).1)
    | _, isFalse notEqual =>
      isFalse (λ equality => notEqual (RawAST.fn.inj equality).2)

end AST

open AST

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE : LE (AST.Typ P) := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
@[instance_reducible]
instance typDecidableLE : DecidableLE (AST.Typ P) := λ left right =>
  match AST.rawTypDecidableEq left.raw right.raw with
  | isTrue equality => isTrue (AST.extRaw equality)
  | isFalse notEqual =>
    isFalse (λ equality => notEqual (congrArg (λ typ => typ.raw) equality))



/--
Shares one receipt carrier between executable values and build-time types.

The underlying view stores a tagged value-or-type payload. Runtime and build
contexts refine that view independently through [UIdEquiv.Lesser]. The subtype
proof certifies which payload is available, but [AST.ref] stores only the raw
receipt. Projecting a lambda argument to `.val` therefore discards that proof, so
this infrastructure alone does not prevent phase-dependent lambda bodies.
-/
class TypOrValRefs extends HasData where --FIXME: rename to ValOrTypRefs
  uid2either : UIdView (λ T =>
    let P : Parameters := { C := T, D := D }

    AST.Val P ⊕ AST.Typ P
  )

namespace TypOrValRefs
section variable (self : TypOrValRefs)

/-- The shared syntax parameters are fixed by the mixed receipt view. -/
abbrev Parameters : Parameters := { C := self.uid2either.UId, D := self.D }

end
end TypOrValRefs

/-- Owns the runtime receipt bridge for executable STLC values. -/
class ExeEnv (refs : TypOrValRefs) where
  uid2valCtx : UIdEquiv.Lesser (base := refs.uid2either)
    (Sum.inl : AST.Val refs.Parameters →
      AST.Val refs.Parameters ⊕ AST.Typ refs.Parameters)

namespace AST

/-- Evaluates executable terms whose references carry receipts from the runtime context. -/
def eval [refs : TypOrValRefs] [env : ExeEnv refs]
    (self : Trm refs.Parameters) : RecOpt (Val refs.Parameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      let anf := (eval fnTerm fuel, eval arg fuel)
      match anf with
      | (.yield (some (.lam body _tIn)), .yield (some input)) =>
        let receipt := env.uid2valCtx.inv input
        eval (body receipt) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref receipt =>
      match refs.uid2either.get receipt with
      | .inl value => .yield (some value)
      | .inr _typ => .yield none

end AST

end

end Lp2lc.Active.STLC
