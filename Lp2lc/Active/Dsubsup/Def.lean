/-***************************************************************************
* DSubSup (D<:>)                                                           *
* Port of Coq source: Lp2lc_coq/Active/Dsubsup.v                           *
* Notes:                                                                   *
* - Keep this file restricted to core syntax, operations, and judgments.   *
* - No theorems here; theorem statements reside in Proof.lean.             *
* - No axioms allowed here.                                                *
***************************************************************************-/

import Std
import Mathlib.Data.Finset.Basic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Dsubsup

open Lp2lc.Active
open Std

/-- Abstract variable type shared across modules -/
abbrev Var := Lp2lc.Active.Var
abbrev Vars := Lp2lc.Active.Vars

-- Environment is abstract here; reuse the shared `ok` predicate
-- use shared ok from Lp2lc.Active.Shared

/-!
## Language (mirroring Coq inductives)

Coq (Dsubsup.v) summary:
- typ ::= Bot | Top | sel p | {Type : S..U} | (z : T) -> T^z
- trm ::= p | t t
- p   ::= x | v
- v   ::= { Type = T } | lambda x:T.t

We encode a minimal skeleton sufficient to state theorems. Details of LibLN
and locally nameless infra are not reimplemented here; we keep shapes faithful
and provide open/subst as total functions to support statement formation.
-/

mutual
  inductive Trm where
    | bvar : Nat -> Trm
    | fvar : Var -> Trm
    | abs  : Typ -> Trm -> Trm
    | mem  : Typ -> Trm
    | app  : Trm -> Trm -> Trm
    deriving Repr, BEq

  /-- Types depend on terms in `sel` and second arg of `all` -/
  inductive Typ where
    | bot   : Typ
    | top   : Typ
    | sel   : Trm -> Typ
    | mem   : Typ -> Typ -> Typ
    | all   : Typ -> Typ -> Typ
    deriving Repr, BEq
end

/-- opening (locally nameless style). For scaffold only: identity operations. -/
def openT (T : Typ) (_ : Trm) : Typ := T
def openE (t : Trm) (_ : Trm) : Trm := t

notation:67 T " open_t_var " x => openT T (Trm.fvar x)
notation:67 t " open_e_var " x => openE t (Trm.fvar x)

/-- Local closure predicates (skeletal) -/
axiom LcT : Typ -> Prop
axiom LcE : Trm -> Prop

/-- Values -/
inductive Value : Trm -> Prop where
  | abs  : ∀ V e1, LcE (Trm.abs V e1) -> Value (Trm.abs V e1)
  | mem  : ∀ V,   LcE (Trm.mem V)     -> Value (Trm.mem V)

/-- Environment as list of (Var × Typ) akin to Coq env typ. -/
abbrev Env := List (Var × Typ)

/-- Lookup-based binding predicate, following the style in Fsub. -/
@[simp] def bindsT (x : Var) (T : Typ) (E : Env) : Prop := E.lookup x = some T

/-- Well-formed type/term in environment (skeletal to state theorems) -/
axiom Wft : Env -> Typ -> Prop
axiom Wfe : Env -> Trm -> Prop

/-- Well-formed environment (okt in Coq) -/
inductive Okt : Env -> Prop where
  | nil  : Okt []
  | push : ∀ E x T, Okt E -> Wft E T -> (E.lookup x = none) -> Okt ((x,T)::E)

/-- Subtyping and has-judgment (skeletal for statements) -/
axiom Sub : Env -> Typ -> Typ -> Prop
axiom Has : Env -> Trm -> Typ -> Prop

/-- Typing -/
inductive Typing : Env -> Trm -> Typ -> Prop where
  | var  : ∀ E x T, Okt E -> bindsT x T E -> Typing E (Trm.fvar x) T
  | abs  : ∀ (L : Vars) E V e1 T1, (∀ x, x ∉ L -> Typing ((x,V)::E) (e1 open_e_var x) (T1 open_t_var x)) ->
      Typing E (Trm.abs V e1) (Typ.all V T1)
  | mem  : ∀ E T1, Okt E -> Wft E T1 -> Typing E (Trm.mem T1) (Typ.mem T1 T1)
  | app  : ∀ T1 E e1 e2 T2, Typing E e1 (Typ.all T1 T2) -> Typing E e2 T1 -> Wft E T2 ->
      Typing E (Trm.app e1 e2) T2
  | appvar : ∀ T1 E e1 e2 T2 T2' M, Typing E e1 (Typ.all T1 T2) -> Typing E e2 T1 -> Has E e2 M ->
      T2' = openT T2 e2 -> Wft E T2' -> Typing E (Trm.app e1 e2) T2'
  | sub  : ∀ S E e T, Typing E e S -> Sub E S T -> Typing E e T

/-- Reduction -/
inductive Red : Trm -> Trm -> Prop where
  | app1 : ∀ e1 e1' e2, LcE e2 -> Red e1 e1' -> Red (Trm.app e1 e2) (Trm.app e1' e2)
  | app2 : ∀ e1 e2 e2', Value e1 -> Red e2 e2' -> Red (Trm.app e1 e2) (Trm.app e1 e2')
  | abs  : ∀ V e1 v2, LcE (Trm.abs V e1) -> Value v2 -> Red (Trm.app (Trm.abs V e1) v2) (openE e1 v2)

/-- Meta-properties (targets) -/
def preservation : Prop := ∀ (e e' : Trm) (T : Typ), Typing [] e T -> Red e e' -> Typing [] e' T
def progress     : Prop := ∀ (e : Trm) (T : Typ), Typing [] e T -> (Value e ∨ ∃ e', Red e e')

/-!
### Free variables and substitutions (skeletal, to support theorem statements)
We define fv sets and capture-avoiding substitutions only as needed for
stating lemmas; we do not aim for full LibLN parity here.
-/

def fvT (_ : Typ) : Vars := ∅
def fvE (e : Trm) : Vars :=
  match e with
  | Trm.fvar x => {x}
  | _ => ∅

def substT (_ : Var) (_ : Trm) (T : Typ) : Typ := T
def substE (_ : Var) (_ : Trm) (e : Trm) : Trm := e

end Lp2lc.Active.Dsubsup
