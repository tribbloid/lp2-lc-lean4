import Std
import Mathlib.Data.Finset.Basic

import Aesop
import «Lp2lc».Active.Shared

/-
Automated scaffold for converting Coq source Lp2lc_coq/Active/FsubL_alt.v to Lean 4.
All declarations are ordered as in the Coq file and are preceded by strictly
increasing Coq line-number comments.
Do NOT place theorems here. This file contains only data types and definitions.
-/

open Lp2lc.Active

namespace Lp2lc.Active.FsubL_alt

-- line 30
inductive Typ : Type where
  | typ_top   : Typ
  | typ_bot   : Typ
  | typ_bvar  : Nat → Typ
  | typ_fvar  : Var → Typ
  | typ_arrow : Typ → Typ → Typ
  | typ_all   : Typ → Typ → Typ → Typ

deriving instance Repr, DecidableEq for Typ

-- line 40
inductive Trm : Type where
  | trm_bvar : Nat → Trm
  | trm_fvar : Var → Trm
  | trm_abs  : Typ → Trm → Trm
  | trm_app  : Trm → Trm → Trm
  | trm_tabs : Typ → Typ → Trm → Trm
  | trm_tapp : Trm → Typ → Trm

deriving instance Repr, DecidableEq for Trm

-- line 50
def open_tt_rec (K : Nat) (U : Typ) (T : Typ) : Typ :=
  match T with
  | Typ.typ_top           => Typ.typ_top
  | Typ.typ_bot           => Typ.typ_bot
  | Typ.typ_bvar J        => if K = J then U else (Typ.typ_bvar J)
  | Typ.typ_fvar X        => Typ.typ_fvar X
  | Typ.typ_arrow T1 T2   => Typ.typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | Typ.typ_all T0 T1 T2  => Typ.typ_all (open_tt_rec K U T0) (open_tt_rec K U T1) (open_tt_rec (K + 1) U T2)

-- line 60
def open_tt (T : Typ) (U : Typ) : Typ := open_tt_rec 0 U T

-- line 64
def open_te_rec (K : Nat) (U : Typ) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i        => Trm.trm_bvar i
  | Trm.trm_fvar x        => Trm.trm_fvar x
  | Trm.trm_abs V e1      => Trm.trm_abs (open_tt_rec K U V) (open_te_rec K U e1)
  | Trm.trm_app e1 e2     => Trm.trm_app (open_te_rec K U e1) (open_te_rec K U e2)
  | Trm.trm_tabs VS VU e1 => Trm.trm_tabs (open_tt_rec K U VS) (open_tt_rec K U VU) (open_te_rec (K + 1) U e1)
  | Trm.trm_tapp e1 V     => Trm.trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)

-- line 74
def open_te (t : Trm) (U : Typ) : Trm := open_te_rec 0 U t

-- line 78
def open_ee_rec (k : Nat) (f : Trm) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i        => if k = i then f else (Trm.trm_bvar i)
  | Trm.trm_fvar x        => Trm.trm_fvar x
  | Trm.trm_abs V e1      => Trm.trm_abs V (open_ee_rec (k + 1) f e1)
  | Trm.trm_app e1 e2     => Trm.trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | Trm.trm_tabs VS VU e1 => Trm.trm_tabs VS VU (open_ee_rec k f e1)
  | Trm.trm_tapp e1 V     => Trm.trm_tapp (open_ee_rec k f e1) V

-- line 88
def open_ee (t : Trm) (u : Trm) : Trm := open_ee_rec 0 u t

-- line 92
notation:67 T " open_tt_var " X => open_tt T (Typ.typ_fvar X)
-- line 93
notation:67 t " open_te_var " X => open_te t (Typ.typ_fvar X)
-- line 94
notation:67 t " open_ee_var " x => open_ee t (Trm.trm_fvar x)

-- line 98
inductive DefType : Typ → Prop where
  | type_top :
      DefType Typ.typ_top
  | type_bot :
      DefType Typ.typ_bot
  | type_var : (X : Var) →
      DefType (Typ.typ_fvar X)
  | type_arrow : (T1 T2 : Typ) →
      DefType T1 →
      DefType T2 →
      DefType (Typ.typ_arrow T1 T2)
  | type_all : (L : Vars) → (T0 T1 T2 : Typ) →
      DefType T0 →
      DefType T1 →
      (∀ (X : Var), X ∉ L → DefType (T2 open_tt_var X)) →
      DefType (Typ.typ_all T0 T1 T2)

-- line 117
inductive DefTerm : Trm → Prop where
  | term_var : (x : Var) →
      DefTerm (Trm.trm_fvar x)
  | term_abs : (L : Vars) → (V : Typ) → (e1 : Trm) →
      DefType V →
      (∀ (x : Var), x ∉ L → DefTerm (e1 open_ee_var x)) →
      DefTerm (Trm.trm_abs V e1)
  | term_app : (e1 e2 : Trm) →
      DefTerm e1 →
      DefTerm e2 →
      DefTerm (Trm.trm_app e1 e2)
  | term_tabs : (L : Vars) → (VS VU : Typ) → (e1 : Trm) →
      DefType VS →
      DefType VU →
      (∀ (X : Var), X ∉ L → DefTerm (e1 open_te_var X)) →
      DefTerm (Trm.trm_tabs VS VU e1)
  | term_tapp : (e1 : Trm) → (V : Typ) →
      DefTerm e1 →
      DefType V →
      DefTerm (Trm.trm_tapp e1 V)

-- line 140
inductive Bind : Type where
  | bind_sub : Typ → Typ → Bind
  | bind_typ : Typ → Bind

deriving instance Repr, DecidableEq for Bind

-- line 146
abbrev Env := List (Var × Bind)

-- line 153 (dom/binds helpers)
open Lp2lc.Active

def dom (E : Env) : Vars := Env.domOf E

-- from LibLN
-- line 159
def binds (x : Var) (b : Bind) (E : Env) : Prop := E.lookup x = some b

-- line 153 (Wft) continued per Coq ordering
inductive Wft : Env → Typ → Prop where
  | wft_top : (E : Env) →
      Wft E Typ.typ_top
  | wft_bot : (E : Env) →
      Wft E Typ.typ_bot
  | wft_var : (T0 T1 : Typ) → (E : Env) → (X : Var) →
      binds X (Bind.bind_sub T0 T1) E →
      Wft E (Typ.typ_fvar X)
  | wft_arrow : (E : Env) → (T1 T2 : Typ) →
      Wft E T1 →
      Wft E T2 →
      Wft E (Typ.typ_arrow T1 T2)
  | wft_all : (L : Vars) → (E : Env) → (T0 T1 T2 : Typ) →
      Wft E T0 →
      Wft E T1 →
      (∀ (X : Var), X ∉ L →
        Wft ((X, Bind.bind_sub T0 T1) :: E) (T2 open_tt_var X)) →
      Wft E (Typ.typ_all T0 T1 T2)

-- placeholder shared ok is imported from Shared
-- use shared ok from Lp2lc.Active.Shared

-- line 176
inductive Okt : Env → Prop where
  | okt_empty :
      Okt []
  | okt_sub : (E : Env) → (X : Var) → (T0 T1 : Typ) →
      Okt E → Wft E T0 → Wft E T1 → E.lookup X = none → Okt ((X, Bind.bind_sub T0 T1) :: E)
  | okt_typ : (E : Env) → (x : Var) → (T : Typ) →
      Okt E → Wft E T → E.lookup x = none → Okt ((x, Bind.bind_typ T) :: E)

-- line 186
inductive Sub : Env → Typ → Typ → Prop where
  | sub_top : (E : Env) → (S : Typ) →
      Okt E →
      Wft E S →
      Sub E S Typ.typ_top
  | sub_bot : (E : Env) → (T : Typ) →
      Okt E →
      Wft E T →
      Sub E Typ.typ_bot T
  | sub_refl_tvar : (E : Env) → (X : Var) →
      Okt E →
      Wft E (Typ.typ_fvar X) →
      Sub E (Typ.typ_fvar X) (Typ.typ_fvar X)
  | sub_tvar : (T0 T1 : Typ) → (E : Env) → (X : Var) →
      Okt E →
      binds X (Bind.bind_sub T0 T1) E →
      Sub E (Typ.typ_fvar X) T1
  | sub_tvar_lower : (T0 T1 : Typ) → (E : Env) → (X : Var) →
      Okt E →
      binds X (Bind.bind_sub T0 T1) E →
      Sub E T0 (Typ.typ_fvar X)
  | sub_arrow : (E : Env) → (S1 S2 T1 T2 : Typ) →
      Sub E T1 S1 →
      Sub E S2 T2 →
      Sub E (Typ.typ_arrow S1 S2) (Typ.typ_arrow T1 T2)
  | sub_all : (L : Vars) → (E : Env) → (S0 S1 S2 T0 T1 T2 : Typ) →
      Sub E S0 T0 →
      Sub E T1 S1 →
      (∀ (X : Var), X ∉ L →
          Sub ((X, Bind.bind_sub T0 T1) :: E) (S2 open_tt_var X) (T2 open_tt_var X)) →
      Sub E (Typ.typ_all S0 S1 S2) (Typ.typ_all T0 T1 T2)
  | sub_trans : (E : Env) → (S T U : Typ) →
      Sub E S T →
      Sub E T U →
      Sub E S U

-- line 225
inductive Typing : Env → Trm → Typ → Prop where
  | typing_var : (E : Env) → (x : Var) → (T : Typ) →
      Okt E →
      binds x (Bind.bind_typ T) E →
      Typing E (Trm.trm_fvar x) T
  | typing_abs : (L : Vars) → (E : Env) → (V : Typ) → (e1 : Trm) → (T1 : Typ) →
      (∀ (x : Var), x ∉ L →
        Typing ((x, Bind.bind_typ V) :: E) (e1 open_ee_var x) T1) →
      Typing E (Trm.trm_abs V e1) (Typ.typ_arrow V T1)
  | typing_app : (T1 : Typ) → (E : Env) → (e1 e2 : Trm) → (T2 : Typ) →
      Typing E e1 (Typ.typ_arrow T1 T2) →
      Typing E e2 T1 →
      Typing E (Trm.trm_app e1 e2) T2
  | typing_tabs : (L : Vars) → (E : Env) → (VS VU : Typ) → (e1 : Trm) → (T1 : Typ) →
      (∀ (X : Var), X ∉ L →
        Typing ((X, Bind.bind_sub VS VU) :: E) (e1 open_te_var X) (T1 open_tt_var X)) →
      Typing E (Trm.trm_tabs VS VU e1) (Typ.typ_all VS VU T1)
  | typing_tapp : (T0 T1 : Typ) → (E : Env) → (e1 : Trm) → (T T2 : Typ) →
      Typing E e1 (Typ.typ_all T0 T1 T2) →
      Sub E T0 T →
      Sub E T T1 →
      Typing E (Trm.trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : (S : Typ) → (E : Env) → (e : Trm) → (T : Typ) →
      Typing E e S →
      Sub E S T →
      Typing E e T

-- line 254
inductive Value : Trm → Prop where
  | value_abs  : (V : Typ) → (e1 : Trm) → DefTerm (Trm.trm_abs V e1) →
                 Value (Trm.trm_abs V e1)
  | value_tabs : (VS VU : Typ) → (e1 : Trm) → DefTerm (Trm.trm_tabs VS VU e1) →
                 Value (Trm.trm_tabs VS VU e1)

-- line 262
inductive Red : Trm → Trm → Prop where
  | red_app_1 : (e1 e1' e2 : Trm) →
      DefTerm e2 →
      Red e1 e1' →
      Red (Trm.trm_app e1 e2) (Trm.trm_app e1' e2)
  | red_app_2 : (e1 e2 e2' : Trm) →
      Value e1 →
      Red e2 e2' →
      Red (Trm.trm_app e1 e2) (Trm.trm_app e1 e2')
  | red_tapp : (e1 e1' : Trm) → (V : Typ) →
      DefType V →
      Red e1 e1' →
      Red (Trm.trm_tapp e1 V) (Trm.trm_tapp e1' V)
  | red_abs : (V : Typ) → (e1 : Trm) → (v2 : Trm) →
      DefTerm (Trm.trm_abs V e1) →
      Value v2 →
      Red (Trm.trm_app (Trm.trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : (V0 V1 : Typ) → (e1 : Trm) → (V2 : Typ) →
      DefTerm (Trm.trm_tabs V0 V1 e1) →
      DefType V2 →
      Red (Trm.trm_tapp (Trm.trm_tabs V0 V1 e1) V2) (open_te e1 V2)

-- line 286
def preservation : Prop := ∀ (e e' : Trm) (T : Typ),
  Typing [] e T →
  Red e e' →
  Typing [] e' T

-- line 291
def progress : Prop := ∀ (e : Trm) (T : Typ),
  Typing [] e T →
  Value e ∨ (∃ e', Red e e')

-- line 305
def fv_tt (T : Typ) : Vars :=
  match T with
  | Typ.typ_top           => ∅
  | Typ.typ_bot           => ∅
  | Typ.typ_bvar _        => ∅
  | Typ.typ_fvar X        => {X}
  | Typ.typ_arrow T1 T2   => (fv_tt T1) ∪ (fv_tt T2)
  | Typ.typ_all T0 T1 T2  => (fv_tt T0) ∪ (fv_tt T1) ∪ (fv_tt T2)

-- line 317
def fv_te (e : Trm) : Vars :=
  match e with
  | Trm.trm_bvar _        => ∅
  | Trm.trm_fvar _        => ∅
  | Trm.trm_abs V e1      => (fv_tt V) ∪ (fv_te e1)
  | Trm.trm_app e1 e2     => (fv_te e1) ∪ (fv_te e2)
  | Trm.trm_tabs VS VU e1 => (fv_tt VS) ∪ (fv_tt VU) ∪ (fv_te e1)
  | Trm.trm_tapp e1 V     => (fv_tt V) ∪ (fv_te e1)

-- line 329
def fv_ee (e : Trm) : Vars :=
  match e with
  | Trm.trm_bvar _        => ∅
  | Trm.trm_fvar x        => {x}
  | Trm.trm_abs _ e1      => (fv_ee e1)
  | Trm.trm_app e1 e2     => (fv_ee e1) ∪ (fv_ee e2)
  | Trm.trm_tabs _ _ e1   => (fv_ee e1)
  | Trm.trm_tapp e1 _     => (fv_ee e1)

-- line 341
def subst_tt (Z : Var) (U : Typ) (T : Typ) : Typ :=
  match T with
  | Typ.typ_top           => Typ.typ_top
  | Typ.typ_bot           => Typ.typ_bot
  | Typ.typ_bvar J        => Typ.typ_bvar J
  | Typ.typ_fvar X        => by
      classical
      exact (if h : X = Z then (by simpa [h] using U) else Typ.typ_fvar X)
  | Typ.typ_arrow T1 T2   => Typ.typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | Typ.typ_all T0 T1 T2  => Typ.typ_all (subst_tt Z U T0) (subst_tt Z U T1) (subst_tt Z U T2)

-- line 353
def subst_te (Z : Var) (U : Typ) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i        => Trm.trm_bvar i
  | Trm.trm_fvar x        => Trm.trm_fvar x
  | Trm.trm_abs V e1      => Trm.trm_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | Trm.trm_app e1 e2     => Trm.trm_app  (subst_te Z U e1) (subst_te Z U e2)
  | Trm.trm_tabs VS VU e1 => Trm.trm_tabs (subst_tt Z U VS) (subst_tt Z U VU) (subst_te Z U e1)
  | Trm.trm_tapp e1 V     => Trm.trm_tapp (subst_te Z U e1) (subst_tt Z U V)

-- line 365
def subst_ee (z : Var) (u : Trm) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i        => Trm.trm_bvar i
  | Trm.trm_fvar x        => by
      classical
      exact (if h : x = z then (by simpa [h] using u) else Trm.trm_fvar x)
  | Trm.trm_abs V e1      => Trm.trm_abs V (subst_ee z u e1)
  | Trm.trm_app e1 e2     => Trm.trm_app (subst_ee z u e1) (subst_ee z u e2)
  | Trm.trm_tabs VS VU e1 => Trm.trm_tabs VS VU (subst_ee z u e1)
  | Trm.trm_tapp e1 V     => Trm.trm_tapp (subst_ee z u e1) V

-- line 377
def subst_tb (Z : Var) (P : Typ) (b : Bind) : Bind :=
  match b with
  | Bind.bind_sub T0 T1 => Bind.bind_sub (subst_tt Z P T0) (subst_tt Z P T1)
  | Bind.bind_typ T     => Bind.bind_typ (subst_tt Z P T)

-- Map type substitution over an environment (helper for proofs)
-- Derived from LibEnv-style map composition
-- Note: This mirrors Fsub map_subst_tb with pair mapping
-- line 383
def map_subst_tb (Z : Var) (P : Typ) (E : Env) : Env :=
  E.map (fun p => match p with
    | (x, Bind.bind_typ T)     => (x, Bind.bind_typ (subst_tt Z P T))
    | (x, Bind.bind_sub T0 T1) => (x, Bind.bind_sub (subst_tt Z P T0) (subst_tt Z P T1)))

-- line 1512 (start of PossibleTypes def block in proofs section)
-- We place the relation here for reuse by theorems.
inductive PossibleTypes : Trm → Typ → Prop where
  | pt_top : (v : Trm) → Value v → PossibleTypes v Typ.typ_top
  | pt_arrow : (L : Vars) → (V V' : Typ) → (e1 : Trm) → (T1 T1' : Typ) →
      (∀ (x : Var), x ∉ L → Typing ((x, Bind.bind_typ V) :: []) (e1 open_ee_var x) T1) →
      Sub [] V' V →
      Sub [] T1 T1' →
      PossibleTypes (Trm.trm_abs V e1) (Typ.typ_arrow V' T1')
  | pt_all : (L : Vars) → (VS VS' VU VU' : Typ) → (e1 : Trm) → (T1 T1' : Typ) →
      (∀ (X : Var), X ∉ L → Typing ((X, Bind.bind_sub VS VU) :: []) (e1 open_te_var X) (T1 open_tt_var X)) →
      Sub [] VS VS' →
      Sub [] VU' VU →
      (∀ (X : Var), X ∉ L → Sub ((X, Bind.bind_sub VS' VU') :: []) (T1 open_tt_var X) (T1' open_tt_var X)) →
      PossibleTypes (Trm.trm_tabs VS VU e1) (Typ.typ_all VS' VU' T1')

end Lp2lc.Active.FsubL_alt
