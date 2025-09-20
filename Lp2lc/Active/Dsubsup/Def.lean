/-***************************************************************************
* DSubSup (D<:>)                                                           *
* Port of Coq source: Lp2lc_coq/Active/Dsubsup.v                           *
* Notes:                                                                   *
* - Keep this file restricted to core syntax, operations, and judgments.   *
* - No theorems here; theorem statements reside in Proof.lean.             *
* - No axioms allowed here beyond abstract predicates (ok, lc, wf, etc.). *
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

-- Environment as list of (Var × Typ); we reuse the shared `ok` predicate.
-- use shared ok from Lp2lc.Active.Shared
-- NOTE: Env depends on Typ, so we declare it after Typ below.

/-!
## Language (mirroring Coq inductives)

Coq (Dsubsup.v) summary:
- typ ::= Bot | Top | sel p | {Type : S..U} | (z : T) -> T^z
- trm ::= p | t t
- p   ::= x | v
- v   ::= { Type = T } | lambda x:T.t

We encode a skeleton faithful to the Coq shapes sufficient to state theorems.
Locally nameless operations are provided (open/subst/fv) to support statements.
-/

mutual
  inductive Trm where
    | bvar : Nat -> Trm
    | fvar : Var -> Trm
    | abs  : Typ -> Trm -> Trm
    | mem  : Typ -> Trm
    | app  : Trm -> Trm -> Trm
    deriving Repr, BEq, DecidableEq

  /-- Types depend on terms in `sel` and second arg of `all` -/
  inductive Typ where
    | bot   : Typ
    | top   : Typ
    | sel   : Trm -> Typ
    | mem   : Typ -> Typ -> Typ
    | all   : Typ -> Typ -> Typ
    deriving Repr, BEq, DecidableEq
end

/-! ### Opening (locally nameless style)
We define de Bruijn opening at recursion depth k, then wrappers at depth 0. -/
mutual
  def openTRec (k : Nat) (f : Trm) (T : Typ) : Typ :=
    match T with
    | Typ.bot           => Typ.bot
    | Typ.top           => Typ.top
    | Typ.sel t         => Typ.sel (openERec k f t)
    | Typ.mem T1 T2     => Typ.mem (openTRec k f T1) (openTRec k f T2)
    | Typ.all T1 T2     => Typ.all (openTRec k f T1) (openTRec (k+1) f T2)

  def openERec (k : Nat) (f : Trm) (e : Trm) : Trm :=
    match e with
    | Trm.bvar i        => if k = i then f else Trm.bvar i
    | Trm.fvar x        => Trm.fvar x
    | Trm.abs V e1      => Trm.abs (openTRec k f V) (openERec (k+1) f e1)
    | Trm.mem T         => Trm.mem (openTRec k f T)
    | Trm.app e1 e2     => Trm.app (openERec k f e1) (openERec k f e2)
end

def openT (T : Typ) (f : Trm) : Typ := openTRec 0 f T
def openE (t : Trm) (u : Trm) : Trm := openERec 0 u t

notation:67 T " open_t_var " x => openT T (Trm.fvar x)
notation:67 t " open_e_var " x => openE t (Trm.fvar x)

/-- Now that Typ is defined, declare the environment alias. -/
abbrev Env := List (Var × Typ)

/-- Local closure predicates (skeletal) -/
axiom LcT : Typ -> Prop
axiom LcE : Trm -> Prop

/-- Values -/
inductive Value : Trm -> Prop where
  | abs  : ∀ V e1, LcE (Trm.abs V e1) -> Value (Trm.abs V e1)
  | mem  : ∀ V,   LcE (Trm.mem V)     -> Value (Trm.mem V)

/-- Lookup-based binding predicate for environments. -/
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
We define fv sets and capture-avoiding substitutions to mirror Coq structure. -/

mutual
  def fvT (T : Typ) : Vars :=
    match T with
    | Typ.bot           => ∅
    | Typ.top           => ∅
    | Typ.sel t         => fvE t
    | Typ.mem T1 T2     => (fvT T1) ∪ (fvT T2)
    | Typ.all T1 T2     => (fvT T1) ∪ (fvT T2)

  def fvE (e : Trm) : Vars :=
    match e with
    | Trm.bvar _        => ∅
    | Trm.fvar x        => {x}
    | Trm.abs V e1      => (fvT V) ∪ (fvE e1)
    | Trm.mem T1        => fvT T1
    | Trm.app e1 e2     => (fvE e1) ∪ (fvE e2)
end

mutual
  def substT (z : Var) (u : Trm) (T : Typ) : Typ :=
    match T with
    | Typ.bot           => Typ.bot
    | Typ.top           => Typ.top
    | Typ.sel t         => Typ.sel (substE z u t)
    | Typ.mem T1 T2     => Typ.mem (substT z u T1) (substT z u T2)
    | Typ.all T1 T2     => Typ.all (substT z u T1) (substT z u T2)

  def substE (z : Var) (u : Trm) (e : Trm) : Trm :=
    match e with
    | Trm.bvar i        => Trm.bvar i
    | Trm.fvar x        => by
        classical
        exact (if h : x = z then (by simpa [h] using u) else Trm.fvar x)
    | Trm.abs V e1      => Trm.abs (substT z u V) (substE z u e1)
    | Trm.mem T1        => Trm.mem (substT z u T1)
    | Trm.app e1 e2     => Trm.app (substE z u e1) (substE z u e2)
end

/-- Map a term-substitution on types across an environment. -/
def mapSubst (Z : Var) (u : Trm) (E : Env) : Env :=
  Env.mapSecond (fun T => substT Z u T) E

/- Additional inductives that appear in Coq within the proofs ---------------- -/

/-- Pseudo-subtyping under empty environment (used in canonical forms). -/
inductive PSub : Typ -> Typ -> Prop :=
  | bot  : ∀ U, Wft [] U -> PSub Typ.bot U
  | top  : ∀ S, Wft [] S -> PSub S Typ.top
  | refl_sel : ∀ t, Wft [] (Typ.sel t) -> PSub (Typ.sel t) (Typ.sel t)
  | sel1 : ∀ U, Wft [] U -> PSub (Typ.sel (Trm.mem U)) U
  | sel2 : ∀ S, Wft [] S -> PSub S (Typ.sel (Trm.mem S))
  | mem  : ∀ S1 U1 S2 U2, PSub S2 S1 -> PSub U1 U2 -> PSub (Typ.mem S1 U1) (Typ.mem S2 U2)
  | all  : ∀ (L : Vars) S1 S2 T1 T2,
      PSub T1 S1 -> (∀ x, x ∉ L -> Sub ((x, T1)::[]) (S2 open_t_var x) (T2 open_t_var x)) ->
      PSub (Typ.all S1 S2) (Typ.all T1 T2)
  | trans : ∀ S T U, PSub S T -> PSub T U -> PSub S U

/-- Possible types for values (indexed by a fuel n). -/
inductive PossibleTypes : Nat -> Trm -> Typ -> Prop :=
  | top : ∀ n v, Value v -> Wfe [] v -> PossibleTypes n v Typ.top
  | mem : ∀ n T S U, PSub S T -> PSub T U -> PossibleTypes n (Trm.mem T) (Typ.mem S U)
  | all : ∀ (L : Vars) n V V' e1 T1 T1',
      (∀ X, X ∉ L -> Typing ((X, V)::[]) (e1 open_e_var X) (T1 open_t_var X)) ->
      PSub V' V ->
      (∀ X, X ∉ L -> Sub ((X, V')::[]) (T1 open_t_var X) (T1' open_t_var X)) ->
      PossibleTypes (Nat.succ n) (Trm.abs V e1) (Typ.all V' T1')
  | all_shallow : ∀ V V' e1 T1', Wfe [] (Trm.abs V e1) -> Wft [] (Typ.all V' T1') ->
      PossibleTypes 0 (Trm.abs V e1) (Typ.all V' T1')
  | sel : ∀ n v S, PossibleTypes n v S -> PossibleTypes n v (Typ.sel (Trm.mem S))

end Lp2lc.Active.Dsubsup
