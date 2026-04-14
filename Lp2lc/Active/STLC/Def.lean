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

mutual

/--
syntax only, without consistency check, some Typ/Trm structure won't make sense (e.g. applying a literal on a variable)
a generator of Trm AST for any index type, akin to a free monad in Scala

CAUTION: every declaration in code must be included in this AST
regardless of index! E.g. the AST for the monoFunction `{(x : In) => fn(x)}` must
contain `In` all the time (otherwise it become a polyFunction)

-/
inductive Trm : Type
| var : Index -> (tAnnotation: TypProto) -> Trm
  -- not in core STLC, but included anyway to make it practical
| literal : Instructions -> Trm
  -- mono function that should break if applied on arg of different type (comparing to tIn)
  -- polymorphic/generic/dependent functions will have similar AST but without tIn
| monoFunction : ((argument : Index) -> Trm) -> (tIn: TypProto) -> Trm
  -- mono application
| apply : (function : Trm) -> (argument : Trm) -> Trm

inductive TypProto : Type
| base : TypProto
| arrow : (tIn : TypProto) → (tOut : TypProto) → TypProto

end

end

abbrev Typ := TypProto Unit


-- wildcard `Trm ?` lookup
-- .var is deliberately impossible to construct except inside a function body
-- others are fine
abbrev ClosedTrm := (Index : Type) -> Trm Index

def ClosedTrm.Typed(self: ClosedTrm) := self Typ

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

/--
convert a syntactic Typ AST into a semantic one
-/
def HasType (t: Typ) : Semantic.Typ := sorry

/--
recursively evaluate a closed term using an operational/definitional interpreter
return some if successful
return none if the term is ill-formed, ill-typed or running out of fuel
use `Later` and fuel modality to avoid infinite loop
-/
def BigStepRuntimeEval: (fuel : Nat) → ClosedTrm → Option ClosedTrm := sorry

end STLC
