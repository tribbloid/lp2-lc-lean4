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

namespace Pre
section

variable (Index : Type) [DecidableEq Index]

-- syntax only, without consistency check, some Pre.Typ/Pre.Trm structure won't make sense (e.g. applying a literal)
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

end Pre

-- Polymorphic closed term
abbrev Trm: Type 1 := (index : Type) -> Pre.Trm index

-- Helper constructors are not possible for polymorphic PHOAS functions without rank-n typing wrapping,
-- use Pre.Trm constructors directly for locally closed terms.

example : Trm := fun _index => Pre.Trm.function (fun var => Pre.Trm.var var)

-- ditto
abbrev Typ := Pre.Typ

scoped infixr:60 " :=> " => Pre.Typ.arrow

namespace Semantic

-- semantic type is a generator of evidence that a term can inhabit it
-- union and intersection types can be expressed directly.
def Typ := Trm -> Prop

-- A bound determines whether a type fits somewhere in the subtyping Heyting
-- algebra; this is not useful for core STLC so far.
-- bound is a (mostly implicit) term in Scala (`ev: T <:< Int`)
def Bound := Typ -> Prop

end Semantic

inductive HasType : Pre.Trm Pre.Typ → Pre.Typ → Prop where
  | var {t : Pre.Typ} : HasType (.var t) t
  | literal {i : Instructions} {t : Pre.Typ} : HasType (.literal i) t
  | app {tIn tOut : Pre.Typ} {f x : Pre.Trm Pre.Typ} :
      HasType f (Pre.Typ.arrow tIn tOut) → HasType x tIn → HasType (.apply f x) tOut
  | function {tIn tOut : Pre.Typ} {e : Pre.Typ → Pre.Trm Pre.Typ} :
      HasType (e tIn) tOut → HasType (.function e) (Pre.Typ.arrow tIn tOut)

abbrev ClosedHasType (E : Trm) (t : Typ) : Prop :=
  HasType (E Pre.Typ) t

end Lp2lc.Active.STLC
