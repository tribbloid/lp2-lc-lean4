namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

abbrev Index := Type -- AKA symbol, PHOAS carrier
def ByteCode := String

section Syntax -- uses weak HOAS/PHOAS convention

variable (I : Index) -- index

mutual

inductive Typ : Index where -- Type AST
| primitive -- `AnyVal` -- primitive data
| depFn (tIn : Typ) (tOut : (arg : I) → Typ) -- dependent function
| top -- anything/wildcard type, accepts any value.

inductive Trm : Index where -- Term AST, `t` represents the optional type annotation
| val (v : Val) (t : Option Typ := by exact none) -- wrapper of `Val`
| apply (fn : Trm) (arg : Trm) (t : Option Typ := by exact none)
| ref (s: I) (t : Option Typ := by exact none) -- binded variable reference, AKA variable/var

inductive Val : Index where -- Value (both AST and runtime data)
| primitive (repr : ByteCode) -- raw data, can inhabit `Typ.primitive`
| primitiveFn (body: ByteCode -> Trm) -- function that modifes raw data directly, can inhabit `Typ.depFn .primitive fun _ => .primitive`
| fn (body : (arg : I) → Trm) -- function that build a term from index, can inhabit any `Typ.depFn`

end

notation "Hint" => Option Typ

/-- Embeds values as value terms for dot-notation-friendly syntax construction. -/
instance valIsTrm : Coe (Val I) (Trm I) where
  coe := fun v => Trm.val v

/-- Fixed-point bound, a bidirectional lookup between `Index` and actual compiletime/runtime representation -/
class FBound (I : Index) (K : (index : Index) → Type) where -- fixed-point cast, looks like a reversed Env, it cast `Trm I` into something Val.depFn can accept
  fwd : (value : K I) → I -- useful in eval, definition uses the inverse but interpreter is not allowed to see it.
  rev : (index : I) → K I
  fwdRoundtrip : (value : K I) → rev (fwd value) = value

attribute [simp] FBound.fwdRoundtrip

/-- Fuel-guarded semantic result used by executable interpreters and compilers. -/
inductive Outcome (T : Index)
| some (v: T)
| error
| outOfFuel

def Outcome.isSome : (self : Outcome T) → Prop
| .some _ => true
| _ => false

namespace Typ

inductive SubtypeEv : (left: Typ I) -> (right: Typ I) -> Prop
| x2x (same: Typ I) : SubtypeEv same same
| x2Top (left : Typ I) : SubtypeEv left Typ.top

end Typ

namespace Trm

/--
Evaluates a source or compiled program by spending 1 fuel at each semantic
descent. Runtime evaluation uses `FBound I Val` for references and deliberately
does not inspect compile-time typing evidence.
-/
def eval {I : Index} [FBound I Val] (trm : Trm I) (fuel : Nat) : Outcome (Val I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val value _ => .some value
    | .apply fn arg _ =>
      let anf := (fn.eval fuel, arg.eval fuel) -- ANF, atomic normal form
      match anf with
      | (.some (.fn body), .some value) =>
        (body (FBound.fwd value)).eval fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .error
    | .ref refValue _ =>
      .some (FBound.rev refValue)

def compile {I : Index} [FBound I Trm] (trm : Trm I) (fuel : Nat) : Outcome (Trm I) := sorry

/-- Semantic typing predicate, defined as successful fuel-guarded compilation. -/
def Typing {I : Index} [FBound I Trm] (trm : Trm I) (fuel : Nat) : Prop :=
  (trm.compile fuel).isSome

end Trm

end Syntax

/-- Closed polymorphic type syntax fixture over any PHOAS index. -/
abbrev TypAST := {I : Index} → Typ I

/-- Closed polymorphic value syntax fixture over any PHOAS index. -/
abbrev ValAST := {I : Index} → Val I

/-- Closed polymorphic term syntax fixture over any PHOAS index. -/
abbrev TrmAST := {I : Index} → Trm I

end DTLC

end Lp2lc.Active
