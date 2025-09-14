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

/-- Environment is abstract here; reuse the shared `ok` predicate -/
notation "ok" => Lp2lc.Active.ok

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

/-- opening (locally nameless style). We provide simple structurally recursive
    total functions; they mimic the Coq `open_t_rec` / `open_e_rec`. -/
mutual
  def openTRec (k : Nat) (f : Trm) (T : Typ) : Typ :=
    match T with
    | Typ.bot       => Typ.bot
    | Typ.top       => Typ.top
    | Typ.sel t     => Typ.sel (openERec k f t)
    | Typ.mem T1 T2 => Typ.mem (openTRec k f T1) (openTRec k f T2)
    | Typ.all T1 T2 => Typ.all (openTRec k f T1) (openTRec (k+1) f T2)

  def openERec (k : Nat) (f : Trm) (e : Trm) : Trm :=
    match e with
    | Trm.bvar i      => if k = i then f else Trm.bvar i
    | Trm.fvar x      => Trm.fvar x
    | Trm.abs V e1    => Trm.abs (openTRec k f V) (openERec (k+1) f e1)
    | Trm.mem T       => Trm.mem (openTRec k f T)
    | Trm.app e1 e2   => Trm.app (openERec k f e1) (openERec k f e2)
end

abbrev openT (T : Typ) (f : Trm) : Typ := openTRec 0 f T
abbrev openE (t : Trm) (u : Trm) : Trm := openERec 0 u t

notation:67 T " open_t_var " x => openT T (Trm.fvar x)
notation:67 t " open_e_var " x => openE t (Trm.fvar x)

/-- Local closure predicates (skeletal) -/
mutual
  inductive LcT : Typ -> Prop where
    | bot : LcT Typ.bot
    | top : LcT Typ.top
    | sel : ∀ e, LcE e -> LcT (Typ.sel e)
    | mem : ∀ T1 T2, LcT T1 -> LcT T2 -> LcT (Typ.mem T1 T2)
    | all : ∀ (L : Vars) (T1 T2), LcT T1 -> (∀ x, x ∉ L -> LcT (T2 open_t_var x)) -> LcT (Typ.all T1 T2)
  
  inductive LcE : Trm -> Prop where
    | var : ∀ x, LcE (Trm.fvar x)
    | abs : ∀ (L : Vars) (V : Typ) (e : Trm), LcT V -> (∀ x, x ∉ L -> LcE (e open_e_var x)) -> LcE (Trm.abs V e)
    | mem : ∀ T, LcT T -> LcE (Trm.mem T)
    | app : ∀ e1 e2, LcE e1 -> LcE e2 -> LcE (Trm.app e1 e2)
end

/-- Values -/
inductive Value : Trm -> Prop where
  | abs  : ∀ V e1, LcE (Trm.abs V e1) -> Value (Trm.abs V e1)
  | mem  : ∀ V,   LcE (Trm.mem V)     -> Value (Trm.mem V)

/-- Environment as list of (Var × Typ) akin to Coq env typ. -/
abbrev Env := List (Var × Typ)

/-- Lookup-based binding predicate, following the style in Fsub. -/
@[simp] def bindsT (x : Var) (T : Typ) (E : Env) : Prop := E.lookup x = some T

/-- Well-formed type/term in environment (skeletal to state theorems) -/
mutual
  inductive Wft : Env -> Typ -> Prop where
    | bot : ∀ E, Wft E Typ.bot
    | top : ∀ E, Wft E Typ.top
    | sel : ∀ E e, (Value e ∨ ∃ x, Trm.fvar x = e) -> Wfe E e -> Wft E (Typ.sel e)
    | mem : ∀ E T1 T2, Wft E T1 -> Wft E T2 -> Wft E (Typ.mem T1 T2)
    | all : ∀ (L : Vars) E T1 T2, Wft E T1 -> (∀ x, x ∉ L -> Wft ((x,T1)::E) (T2 open_t_var x)) -> Wft E (Typ.all T1 T2)
  
  inductive Wfe : Env -> Trm -> Prop where
    | var : ∀ U E x, bindsT x U E -> Wfe E (Trm.fvar x)
    | abs : ∀ (L : Vars) E V e, Wft E V -> (∀ x, x ∉ L -> Wfe ((x,V)::E) (e open_e_var x)) -> Wfe E (Trm.abs V e)
    | mem : ∀ E T, Wft E T -> Wfe E (Trm.mem T)
    | app : ∀ E e1 e2, Wfe E e1 -> Wfe E e2 -> Wfe E (Trm.app e1 e2)
end

/-- Well-formed environment (okt in Coq) -/
inductive Okt : Env -> Prop where
  | nil  : Okt []
  | push : ∀ E x T, Okt E -> Wft E T -> (E.lookup x = none) -> Okt ((x,T)::E)

/-- Subtyping and has-judgment (skeletal for statements) -/
mutual
  inductive Sub : Env -> Typ -> Typ -> Prop where
    | bot : ∀ E T, Okt E -> Wft E T -> Sub E Typ.bot T
    | top : ∀ E S, Okt E -> Wft E S -> Sub E S Typ.top
    | reflSel : ∀ E t, Okt E -> Wft E (Typ.sel t) -> Sub E (Typ.sel t) (Typ.sel t)
    | sel1 : ∀ E S U t, Has E t (Typ.mem S U) -> Sub E (Typ.sel t) U
    | sel2 : ∀ E S U t, Has E t (Typ.mem S U) -> Sub E S (Typ.sel t)
    | mem  : ∀ E S1 U1 S2 U2, Sub E S2 S1 -> Sub E U1 U2 -> Sub E (Typ.mem S1 U1) (Typ.mem S2 U2)
    | all  : ∀ (L : Vars) E S1 S2 T1 T2,
        Sub E T1 S1 -> (∀ x, x ∉ L -> Sub ((x,T1)::E) (S2 open_t_var x) (T2 open_t_var x)) ->
        Sub E (Typ.all S1 S2) (Typ.all T1 T2)
    | trans : ∀ E S T U, Sub E S T -> Sub E T U -> Sub E S U
  
  inductive Has : Env -> Trm -> Typ -> Prop where
    | var  : ∀ E x T, Okt E -> bindsT x T E -> Has E (Trm.fvar x) T
    | mem  : ∀ E T, Okt E -> Wft E T -> Has E (Trm.mem T) (Typ.mem T T)
    | abs  : ∀ E V e T, Okt E -> Wfe E (Trm.abs V e) -> Wft E (Typ.all V T) ->
        Has E (Trm.abs V e) (Typ.all V T)
    | sub  : ∀ E t T U, Has E t T -> Sub E T U -> Has E t U
end

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
notation "preservation" => ∀ (e e' : Trm) (T : Typ), Typing [] e T -> Red e e' -> Typing [] e' T
notation "progress"     => ∀ (e : Trm) (T : Typ), Typing [] e T -> (Value e ∨ ∃ e', Red e e')

/-!
### Free variables and substitutions (skeletal, to support theorem statements)
We define fv sets and capture-avoiding substitutions only as needed for
stating lemmas; we do not aim for full LibLN parity here.
-/

mutual
  def fvT (T : Typ) : Vars :=
    match T with
    | Typ.bot       => ∅
    | Typ.top       => ∅
    | Typ.sel t     => fvE t
    | Typ.mem T1 T2 => (fvT T1) ∪ (fvT T2)
    | Typ.all T1 T2 => (fvT T1) ∪ (fvT T2)

  def fvE (e : Trm) : Vars :=
    match e with
    | Trm.bvar _    => ∅
    | Trm.fvar x    => {x}
    | Trm.abs V e1  => (fvT V) ∪ (fvE e1)
    | Trm.mem T     => fvT T
    | Trm.app e1 e2 => (fvE e1) ∪ (fvE e2)
end

mutual
  def substT (z : Var) (u : Trm) (T : Typ) : Typ :=
    match T with
    | Typ.bot       => Typ.bot
    | Typ.top       => Typ.top
    | Typ.sel t     => Typ.sel (substE z u t)
    | Typ.mem T1 T2 => Typ.mem (substT z u T1) (substT z u T2)
    | Typ.all T1 T2 => Typ.all (substT z u T1) (substT z u T2)

  def substE (z : Var) (u : Trm) (e : Trm) : Trm :=
    match e with
    | Trm.bvar i    => Trm.bvar i
    | Trm.fvar x    => if x = z then u else Trm.fvar x
    | Trm.abs V e1  => Trm.abs (substT z u V) (substE z u e1)
    | Trm.mem T1    => Trm.mem (substT z u T1)
    | Trm.app e1 e2 => Trm.app (substE z u e1) (substE z u e2)
end

end Lp2lc.Active.Dsubsup
