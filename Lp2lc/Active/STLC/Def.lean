import Mathlib.Tactic
import «Lp2lc».Active.Shared
import «Lp2lc».Util

namespace Lp2lc.Active.STLC

/-!
This file defines the simply typed lambda calculus and related compiler
components, with the following conventions:

- parametric higher-order abstract syntax (Pre) representation, namely:
  the indices for term and type variables are irrelevant, so every proof must be
  valid regardless of which index is used.
  - indices are not ID! They are just different ways of categorizing variables,
    it's fine for different types/terms to have identical index (thus `DecidableEq`). Categorizing Terms by
    their tightest type is critical in defining `HasType` predicate
  - There is no variable names or de Bruijn indices.
  - Ever term is locally closed, it's impossible to have dangling variable.
  - There is no data structure representing environment/context variable
    bindings; they are just Lean `def`/`let` bindings.
  - There is no class or data structure representing subtyping hierarchies;
    they are just the Heyting algebra of Lean `Prop`.
- extrinsic/Curry-style type representations: term types are predicates
  instead of built-in indices.
- evaluation is a step-indexed logical relation. The step index is the fuel used to
  reason about functions recursively: a function is safe for `steps` when, for
  any `smaller_steps < steps`, it sends semantically safe inputs to outputs that
  stay safe one guarded step later.

All docstrings use short Scala snippets (under 5 lines) as demonstrations.

Variable names follow these conventions:

- Lean variable for type, proposition and sort of any universe should use PascalCase (e.g. `Env`)
  - inductive cases should use camelCase (because they are constructors)
- Lean variable for terms, functions & data should use camelCase (e.g. `Env.bind`)
  - variable for DOT types, pre-types (which are Lean data) should start with `t` (e.g. tIn, tOut)
- use full name, not acronym or abbreviation
-/

structure Later (step : Prop) : Prop where
  force : step

def Instructions := String

section

variable (Index : Type) [DecidableEq Index]

-- syntax only, without consistency check, some Typ/Trm structure won't make sense (e.g. applying a literal)
inductive Trm : Type
| var : Index -> Trm
| literal : Instructions -> Trm -- not in core STLC, but included anyway to make it practical
| function : ((argument : Index) -> Trm) -> Trm
| apply : (function : Trm) -> (argument : Trm) -> Trm

inductive Typ : Type
| base : Typ
| arrow : (tIn : Typ) → (tOut : Typ) → Typ
deriving DecidableEq, Repr

end

-- wildcard `Trm ?` lookup
-- impossible to define an instance except inside a function body
abbrev ClosedTrm := (Index : Type) -> Trm Index

scoped infixr:60 " :=> " => Typ.arrow

namespace Semantic

-- semantic type is a generator of evidence that a term can inhabit it
-- union and intersection types can be expressed directly.
def Typ := ClosedTrm -> Prop

-- A bound determines whether a type fits somewhere in the subtyping Heyting
-- algebra; this is not useful for core STLC so far.
-- bound is a (mostly implicit) term in Scala (`ev: T <:< Int`)
def Bound := Typ -> Prop

end Semantic

namespace prev

-- equivalent to below, but harder to read
inductive HasTypeProto : (typ: Typ) → (trm: Trm Typ) → Prop where
  | var : HasTypeProto typ (.var typ)
  | literal {i : Instructions} : HasTypeProto .base (.literal i)
  | app {tIn tOut : Typ} {f x : Trm Typ} :
      HasTypeProto (.arrow tIn tOut) f → HasTypeProto tIn x → HasTypeProto tOut (.apply f x)
  | function {tIn tOut : Typ} {e : Typ → Trm Typ} :
      HasTypeProto tOut (e tIn) → HasTypeProto (.arrow tIn tOut) (.function e)

end prev

def HasTypeProto (typ: Typ)(trm: Trm Typ): Prop :=
  match trm with
  | .var typ' =>
      typ' = typ
  | .literal _ =>
      typ = typ
  | .function body =>
      ∃ tIn tOut, typ = (tIn :=> tOut) ∧ HasTypeProto tOut (body tIn)
  | .apply function argument =>
      ∃ tIn, HasTypeProto (tIn :=> typ) function ∧ HasTypeProto tIn argument


def HasType (t: Typ) : Semantic.Typ := fun (E : ClosedTrm) =>
  HasTypeProto t (E Typ)

end Lp2lc.Active.STLC
