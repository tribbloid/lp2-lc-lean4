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
  - There is no variable names or de Bruijn indices, every term/type is a Lean `def`/`let` binding.
  - There is no environment/context: Scala is purely functional and stateless, every lemma must be proven from AST references
  - There is no data structure representing subtyping hierarchies:
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

def Instruction := String

class PHOAS (Ast : Type → Type) : Prop where

/--
closed AST are wildcard generators of PHOAS AST given any index type, akin to a free monad in Scala

.var is deliberately impossible to construct anywhere, only visible inside a function body.
(This is why it is called "closed")
-/
abbrev Closed (Ast : Type → Type) [PHOAS Ast] : Type 1 :=
  (Index : Type) → Ast Index

section Syntax

/-
Definition of AST elements without any judgement, it is
possible to define AST that make no sense (e.g. applying a literal on a variable)

each must have a rigorous correspondence to Scala code regardless of `Index`.
E.g. the AST for the monoFunction `{(x : In) => fn(x) : Out}` must
contain `In` and `Out`, or be reduced to a polyFunction)
-/

variable (Index : Type) [DecidableEq Index] -- compatible with Type0 and Type1

mutual

inductive Trm : Type
| var : Index -> (t: Typ) -> Trm
  /--
  not in core STLC, but included to make it closer to Scala
  `Instruction` is the code snippet (without type annotation) to express the literal.
  ```scala
  val literal = {3: AnyVal}
  ```
  -/
| literal : Instruction -> (t: Typ) -> Trm
  /--
  monomorphic function, can only be applied on arg of type `tIn`.
  ```scala
  val monoFn = {(x: AnyVal) => (x: AnyVal)}
  ```
  -/
| monoFn : ((arg : Index) -> Trm) -> (tIn: Typ) -> (tOut: Typ) -> Trm

  /--
  monomorphic application of a `monoFn`.
  ```scala
  val monoApply = monoFn(literal)
  ```
  -/
| monoApply : (function : Trm) -> (argument : Trm) -> Trm

inductive Typ : Type
/--
AKA primitive type, AnyVal.
```scala
type base = AnyVal
```scala
subtypes of it in both STLC & Scala are ignored, checking them is trivial
-/
| base : Typ
/--
monomorphic arrow, can only be inhabited by `monoFn`
```scala
type monoArrow = (AnyVal => AnyVal)
```
-/
| monoArrow : (tIn : Typ) → (tOut : Typ) → Typ

end

instance : PHOAS Trm where
instance : PHOAS Val where
instance : PHOAS Typ where

def Trm.isValue : Trm Index -> Prop
| (.literal _ _) | (.monoFn _ _ _)  => true
| _ => false

def Val := {v: Trm Index // v.isValue}

end Syntax

scoped infixr:60 " :=> " => Typ.monoArrow

namespace Semantic

-- semantic type is a generator of evidence that a term can inhabit it
-- union and intersection types can be expressed directly.
def Typ : Type 1 := Closed Trm -> Prop

-- A bound determines whether a type fits somewhere in the subtyping Heyting
-- algebra; this is not useful for core STLC so far.
-- bound is a (mostly implicit) term in Scala (`ev: T <:< Int`)
def Bound : Type 1 := Closed STLC.Typ -> Prop

end Semantic

/--
runtime recursive evaluation rule (AKA operational semantic). Scala is a pure functional
language with structural record/object, so small-step imperative evaluation is equivalent to
big-step evaluation on local environment (which is a record) with side effect
- consumes 1 fuel per recursion
- return none if `e` not well-formed (e.g. applying a literal) or ran out of fuel
- return some Val if otherwise
  - even for well-formed but ill-typed expressions (types are erased in runtime).
    In soundness proof this will never happen because ill-typed expressions are rejected early
- not partial evaluation, has no constant folding capability
  - to verify the soundness of partial evaluation, you need to
    write your own definitions of pure function and partial eval rule

(some early formalisation of DOT uses small-step definition with let-binding rule, this style
has been abandoned since 2020)
-/
def Eval: (e: Closed Trm) -> (fuel : Nat) → Option (Closed Val) := sorry

/--
compile-time type checking rule (AKA typing)
- consumes fuel?
- return true if `e` is well-formed and can inhabit `t`
- return false if otherwise
-/
def HasType (e : Closed Trm)(t: Closed Typ) : Prop := sorry

/--
convert a syntactic Typ AST into a semantic one
-/
def ToSemantic (t: Closed Typ): Semantic.Typ := fun (e) => HasType e t

/--
Compile-time type judgement /=> runtime/operational type judgement
-/
def FundamentalLemma : Prop := sorry

end STLC
