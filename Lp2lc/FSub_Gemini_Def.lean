/-***************************************************************************
* Preservation and Progress for System-F with Subtyping - Definitions      *
* Brian Aydemir & Arthur Charguéraud, March 2007                           *
***************************************************************************-/

import Mathlib.Data.Finset.Basic

namespace Lp2lc.FSub

structure Var where
  name : String
deriving Repr, BEq, Hashable, DecidableEq

abbrev Vars := Finset Var

-- line 16
inductive typ : Type where
  | typ_top   : typ
  | typ_bvar  : Nat -> typ
  | typ_fvar  : Var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all   : typ -> typ -> typ

partial def typ.beq : typ -> typ -> Bool
  | .typ_top, .typ_top => true
  | .typ_bvar i, .typ_bvar j => i == j
  | .typ_fvar x, .typ_fvar y => x == y
  | .typ_arrow t1 s1, .typ_arrow t2 s2 => typ.beq t1 t2 && typ.beq s1 s2
  | .typ_all t1 s1, .typ_all t2 s2 => typ.beq t1 t2 && typ.beq s1 s2
  | _, _ => false

instance : BEq typ where
  beq := typ.beq

-- line 25
inductive trm : Type where
  | trm_bvar : Nat -> trm
  | trm_fvar : Var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_tabs : typ -> trm -> trm
  | trm_tapp : trm -> typ -> trm

-- line 35
def open_tt_rec (K : Nat) (U : typ) (T : typ) : typ :=
  match T with
  | typ.typ_top         => typ.typ_top
  | typ.typ_bvar J      => if K = J then U else (typ.typ_bvar J)
  | typ.typ_fvar X      => typ.typ_fvar X
  | typ.typ_arrow T1 T2 => typ.typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ.typ_all T1 T2   => typ.typ_all (open_tt_rec K U T1) (open_tt_rec (K + 1) U T2)

-- line 44
def open_tt (T : typ) (U : typ) : typ := open_tt_rec 0 U T

-- line 48
def open_te_rec (K : Nat) (U : typ) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => trm.trm_bvar i
  | trm.trm_fvar x    => trm.trm_fvar x
  | trm.trm_abs V e1  => trm.trm_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | trm.trm_app e1 e2 => trm.trm_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | trm.trm_tabs V e1 => trm.trm_tabs (open_tt_rec K U V)  (open_te_rec (K + 1) U e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)

-- line 58
def open_te (t : trm) (U : typ) : trm := open_te_rec 0 U t

-- line 62
def open_ee_rec (k : Nat) (f : trm) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => if k = i then f else (trm.trm_bvar i)
  | trm.trm_fvar x    => trm.trm_fvar x
  | trm.trm_abs V e1  => trm.trm_abs V (open_ee_rec (k + 1) f e1)
  | trm.trm_app e1 e2 => trm.trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | trm.trm_tabs V e1 => trm.trm_tabs V (open_ee_rec k f e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (open_ee_rec k f e1) V

-- line 72
def open_ee (t : trm) (u : trm) : trm := open_ee_rec 0 u t

-- line 76
notation:67 T " open_tt_var " X => open_tt T (typ.typ_fvar X)

-- line 77
notation:67 t " open_te_var " X => open_te t (typ.typ_fvar X)

-- line 78
notation:67 t " open_ee_var " x => open_ee t (trm.trm_fvar x)

-- line 82
inductive def_type : typ -> Prop where
  | type_top : def_type typ.typ_top
  | type_var : (X : Var) -> def_type (typ.typ_fvar X)
  | type_arrow : (T1 T2 : typ) -> def_type T1 -> def_type T2 -> def_type (typ.typ_arrow T1 T2)
  | type_all : (L : Vars) -> (T1 T2 : typ) -> def_type T1 -> (∀ (X : Var), X ∉ L -> def_type (T2 open_tt_var X)) -> def_type (typ.typ_all T1 T2)

-- line 98
inductive def_term : trm -> Prop where
  | term_var : (x : Var) -> def_term (trm.trm_fvar x)
  | term_abs : (L : Vars) -> (V : typ) -> (e1 : trm) -> def_type V -> (∀ (x : Var), x ∉ L -> def_term (e1 open_ee_var x)) -> def_term (trm.trm_abs V e1)
  | term_app : (e1 e2 : trm) -> def_term e1 -> def_term e2 -> def_term (trm.trm_app e1 e2)
  | term_tabs : (L : Vars) -> (V : typ) -> (e1 : trm) -> def_type V -> (∀ (X : Var), X ∉ L -> def_term (e1 open_te_var X)) -> def_term (trm.trm_tabs V e1)
  | term_tapp : (e1 : trm) -> (V : typ) -> def_term e1 -> def_type V -> def_term (trm.trm_tapp e1 V)

-- line 122
inductive bind : Type where
  | bind_sub : typ -> bind
  | bind_typ : typ -> bind

partial def bind.beq : bind -> bind -> Bool
  | .bind_sub t1, .bind_sub t2 => typ.beq t1 t2
  | .bind_typ t1, .bind_typ t2 => typ.beq t1 t2
  | _, _ => false

instance : BEq bind where
  beq := bind.beq

-- line 133
abbrev env := List (Var × bind)

-- from LibLN
def binds (x : Var) (b : bind) (E : env) : Prop := E.lookup x = some b

-- line 140
inductive wft : env -> typ -> Prop where
  | wft_top : (E : env) -> wft E typ.typ_top
  | wft_var : (U : typ) -> (E : env) -> (X : Var) ->
      binds X (bind.bind_sub U) E ->
      wft E (typ.typ_fvar X)
  | wft_arrow : (E : env) -> (T1 T2 : typ) ->
      wft E T1 ->
      wft E T2 ->
      wft E (typ.typ_arrow T1 T2)
  | wft_all : (L : Vars) -> (E : env) -> (T1 T2 : typ) ->
      wft E T1 ->
      (∀ (X : Var), X ∉ L -> wft ((X, bind.bind_sub T1) :: E) (T2 open_tt_var X)) ->
      wft E (typ.typ_all T1 T2)

-- line 160
inductive okt : env -> Prop where
  | okt_empty : okt []
  | okt_sub : (E : env) -> (X : Var) -> (T : typ) ->
      okt E -> wft E T -> E.lookup X = none -> okt ((X, bind.bind_sub T) :: E)
  | okt_typ : (E : env) -> (x : Var) -> (T : typ) ->
      okt E -> wft E T -> E.lookup x = none -> okt ((x, bind.bind_typ T) :: E)

-- line 169
inductive sub : env -> typ -> typ -> Prop where
  | sub_top : (E : env) -> (S : typ) ->
      okt E ->
      wft E S ->
      sub E S typ.typ_top
  | sub_refl_tvar : (E : env) -> (X : Var) ->
      okt E ->
      wft E (typ.typ_fvar X) ->
      sub E (typ.typ_fvar X) (typ.typ_fvar X)
  | sub_trans_tvar : (U : typ) -> (E : env) -> (T : typ) -> (X : Var) ->
      binds X (bind.bind_sub U) E ->
      sub E U T ->
      sub E (typ.typ_fvar X) T
  | sub_arrow : (E : env) -> (S1 S2 T1 T2 : typ) ->
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ.typ_arrow S1 S2) (typ.typ_arrow T1 T2)
  | sub_all : (L : Vars) -> (E : env) -> (S1 S2 T1 T2 : typ) ->
      sub E T1 S1 ->
      (∀ (X : Var), X ∉ L ->
          sub ((X, bind.bind_sub T1) :: E) (S2 open_tt_var X) (T2 open_tt_var X)) ->
      sub E (typ.typ_all S1 S2) (typ.typ_all T1 T2)

-- line 195
inductive typing : env -> trm -> typ -> Prop where
  | typing_var : (E : env) -> (x : Var) -> (T : typ) ->
      okt E ->
      binds x (bind.bind_typ T) E ->
      typing E (trm.trm_fvar x) T
  | typing_abs : (L : Vars) -> (E : env) -> (V : typ) -> (e1 : trm) -> (T1 : typ) ->
      (∀ (x : Var), x ∉ L ->
        typing ((x, bind.bind_typ V) :: E) (e1 open_ee_var x) T1) ->
      typing E (trm.trm_abs V e1) (typ.typ_arrow V T1)
  | typing_app : (T1 : typ) -> (E : env) -> (e1 e2 : trm) -> (T2 : typ) ->
      typing E e1 (typ.typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (trm.trm_app e1 e2) T2
  | typing_tabs : (L : Vars) -> (E : env) -> (V : typ) -> (e1 : trm) -> (T1 : typ) ->
      (∀ (X : Var), X ∉ L ->
        typing ((X, bind.bind_sub V) :: E) (e1 open_te_var X) (T1 open_tt_var X)) ->
      typing E (trm.trm_tabs V e1) (typ.typ_all V T1)
  | typing_tapp : (T1 : typ) -> (E : env) -> (e1 : trm) -> (T T2 : typ) ->
      typing E e1 (typ.typ_all T1 T2) ->
      sub E T T1 ->
      typing E (trm.trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : (S : typ) -> (E : env) -> (e : trm) -> (T : typ) ->
      typing E e S ->
      sub E S T ->
      typing E e T

-- line 223
inductive value : trm -> Prop where
  | value_abs  : (V : typ) -> (e1 : trm) -> def_term (trm.trm_abs V e1) -> value (trm.trm_abs V e1)
  | value_tabs : (V : typ) -> (e1 : trm) -> def_term (trm.trm_tabs V e1) -> value (trm.trm_tabs V e1)

-- line 231
inductive red : trm -> trm -> Prop where
  | red_app_1 : (e1 e1' e2 : trm) ->
      def_term e2 ->
      red e1 e1' ->
      red (trm.trm_app e1 e2) (trm.trm_app e1' e2)
  | red_app_2 : (e1 e2 e2' : trm) ->
      value e1 ->
      red e2 e2' ->
      red (trm.trm_app e1 e2) (trm.trm_app e1 e2')
  | red_tapp : (e1 e1' : trm) -> (V : typ) ->
      def_type V ->
      red e1 e1' ->
      red (trm.trm_tapp e1 V) (trm.trm_tapp e1' V)
  | red_abs : (V : typ) -> (e1 : trm) -> (v2 : trm) ->
      def_term (trm.trm_abs V e1) ->
      value v2 ->
      red (trm.trm_app (trm.trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : (V1 : typ) -> (e1 : trm) -> (V2 : typ) ->
      def_term (trm.trm_tabs V1 e1) ->
      def_type V2 ->
      red (trm.trm_tapp (trm.trm_tabs V1 e1) V2) (open_te e1 V2)

-- line 255
def preservation : Prop := ∀ (E : env) (e e' : trm) (T : typ),
  typing E e T ->
  red e e' ->
  typing E e' T

-- line 260
def progress : Prop := ∀ (e : trm) (T : typ),
  typing [] e T ->
  value e ∨ (∃ e', red e e')

-- line 274
partial def fv_tt (T : typ) : Vars :=
  match T with
  | typ.typ_top         => ∅
  | typ.typ_bvar _      => ∅
  | typ.typ_fvar X      => {X}
  | typ.typ_arrow T1 T2 => (fv_tt T1) ∪ (fv_tt T2)
  | typ.typ_all T1 T2   => (fv_tt T1) ∪ (fv_tt T2)

-- line 285
partial def fv_te (e : trm) : Vars :=
  match e with
  | trm.trm_bvar _    => ∅
  | trm.trm_fvar _    => ∅
  | trm.trm_abs V e1  => (fv_tt V) ∪ (fv_te e1)
  | trm.trm_app e1 e2 => (fv_te e1) ∪ (fv_te e2)
  | trm.trm_tabs V e1 => (fv_tt V) ∪ (fv_te e1)
  | trm.trm_tapp e1 V => (fv_tt V) ∪ (fv_te e1)

-- line 297
partial def fv_ee (e : trm) : Vars :=
  match e with
  | trm.trm_bvar _    => ∅
  | trm.trm_fvar x    => {x}
  | trm.trm_abs _ e1  => (fv_ee e1)
  | trm.trm_app e1 e2 => (fv_ee e1) ∪ (fv_ee e2)
  | trm.trm_tabs _ e1 => (fv_ee e1)
  | trm.trm_tapp e1 _ => (fv_ee e1)

-- line 309
partial def subst_tt (Z : Var) (U : typ) (T : typ) : typ :=
  match T with
  | typ.typ_top         => typ.typ_top
  | typ.typ_bvar J      => typ.typ_bvar J
  | typ.typ_fvar X      => if X == Z then U else (typ.typ_fvar X)
  | typ.typ_arrow T1 T2 => typ.typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ.typ_all T1 T2   => typ.typ_all (subst_tt Z U T1) (subst_tt Z U T2)

-- line 320
partial def subst_te (Z : Var) (U : typ) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => trm.trm_bvar i
  | trm.trm_fvar x    => trm.trm_fvar x
  | trm.trm_abs V e1  => trm.trm_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | trm.trm_app e1 e2 => trm.trm_app  (subst_te Z U e1) (subst_te Z U e2)
  | trm.trm_tabs V e1 => trm.trm_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (subst_te Z U e1) (subst_tt Z U V)

-- line 332
partial def subst_ee (z : Var) (u : trm) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => trm.trm_bvar i
  | trm.trm_fvar x    => if x == z then u else (trm.trm_fvar x)
  | trm.trm_abs V e1  => trm.trm_abs V (subst_ee z u e1)
  | trm.trm_app e1 e2 => trm.trm_app (subst_ee z u e1) (subst_ee z u e2)
  | trm.trm_tabs V e1 => trm.trm_tabs V (subst_ee z u e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (subst_ee z u e1) V

-- line 344
def subst_tb (Z : Var) (P : typ) (b : bind) : bind :=
  match b with
  | bind.bind_sub T => bind.bind_sub (subst_tt Z P T)
  | bind.bind_typ T => bind.bind_typ (subst_tt Z P T)

end Lp2lc.FSub
