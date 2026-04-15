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

inductive Ty : Type where
  | bool : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

infixr:60 " ==> " => Ty.arrow

@[simp] def Ty.denote : Ty → Type
  | .bool => Bool
  | .arrow t1 t2 => Ty.denote t1 → Ty.denote t2

inductive Term (var : Ty → Type) : Ty → Type where
  | var : var t → Term var t
  | tru : Term var .bool
  | fals : Term var .bool
  | app : Term var (t1 ==> t2) → Term var t1 → Term var t2
  | abs : (var t1 → Term var t2) → Term var (t1 ==> t2)

abbrev TermClosed (t : Ty) := (var : Ty → Type) → Term var t

@[simp] def Term.denote : {t : Ty} → Term Ty.denote t → Ty.denote t
  | _, .var v => v
  | _, .tru => true
  | _, .fals => false
  | _, .app e1 e2 => (Term.denote e1) (Term.denote e2)
  | _, .abs e => fun x => Term.denote (e x)

@[simp] def TermClosed.denote {t : Ty} (e : TermClosed t) : Ty.denote t :=
  Term.denote (e Ty.denote)

end STLC
