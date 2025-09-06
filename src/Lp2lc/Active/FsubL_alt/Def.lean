
namespace Lp2lc.Active.FsubL_alt

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:30-38
inductive typ : Type :=
  | top : typ
  | bot : typ
  | arr : typ → typ → typ
  | all : typ → typ → typ

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:40-48
inductive trm : Type :=
  | var : Nat → trm
  | app : trm → trm → trm
  | abs : typ → trm → trm
  | tabs : typ → trm → trm
| tapp : trm → typ → trm

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:50-58
def open_tt_rec (K : Nat) (U : typ) (T : typ) : typ :=
  match T with
  | top => top
  | bot => bot
  | arr T1 T2 => arr (open_tt_rec K U T1) (open_tt_rec K U T2)
  | all T1 T2 => all (open_tt_rec K U T1) (open_tt_rec (K + 1) U T2)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:60-60
def open_tt (T U : typ) : typ := open_tt_rec 0 U T

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:64-72
def open_te_rec (K : Nat) (U : typ) (e : trm) : trm :=
  match e with
  | var n => var n
  | app e1 e2 => app (open_te_rec K U e1) (open_te_rec K U e2)
  | abs T e1 => abs (open_tt_rec K U T) (open_te_rec (K + 1) U e1)
  | tabs T e1 => tabs (open_tt_rec K U T) (open_te_rec (K + 1) U e1)
  | tapp e1 T => tapp (open_te_rec K U e1) (open_tt_rec K U T)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:74-74
def open_te (t : trm) (U : typ) : trm := open_te_rec 0 U t

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:78-86
def open_ee_rec (k : Nat) (f e : trm) : trm :=
  match e with
  | var n => if n == k then f else (var n)
  | app e1 e2 => app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | abs T e1 => abs T (open_ee_rec (k + 1) f e1)
  | tabs T e1 => tabs T (open_ee_rec (k + 1) f e1)
  | tapp e1 T => tapp (open_ee_rec k f e1) T

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:88-88
def open_ee (t u : trm) : trm := open_ee_rec 0 u t

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:98-115
inductive type : typ → Prop :=
  | type_top : type top
  | type_bot : type bot
  | type_arr : ∀ T1 T2, type T1 → type T2 → type (arr T1 T2)
  | type_all : ∀ T1 T2, type T1 → (∀ X, type T2) → type (all T1 T2)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:117-138
inductive term : trm → Prop :=
  | term_var : ∀ n, term (var n)
  | term_app : ∀ e1 e2, term e1 → term e2 → term (app e1 e2)
  | term_abs : ∀ T e, type T → (∀ x, term e) → term (abs T e)
  | term_tabs : ∀ T e, type T → (∀ x, term e) → term (tabs T e)
  | term_tapp : ∀ e T, term e → type T → term (tapp e T)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:140-144
inductive bind : Type :=
  | sub : typ → typ → bind
  | typ : typ → bind

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:146-146
def env := List (String × bind)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:153-174
inductive wft : env → typ → Prop :=
  | wft_top : ∀ E, wft E top
  | wft_bot : ∀ E, wft E bot
  | wft_arr : ∀ E T1 T2, wft E T1 → wft E T2 → wft E (arr T1 T2)
  | wft_all : ∀ E T1 T2, wft E T1 → (∀ X, wft E T2) → wft E (all T1 T2)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:176-184
inductive okt : env → Prop :=
  | okt_empty : okt []
  | okt_push : ∀ E x b, okt E → (x ∉ E.keys) → okt ((x, b) :: E)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:186-223
inductive sub : env → typ → typ → Prop :=
  | sub_refl : ∀ E T, wft E T → sub E T T
  | sub_trans : ∀ E S T U, sub E S T → sub E T U → sub E S U
  | sub_top : ∀ E T, wft E T → sub E T top
  | sub_bot : ∀ E T, wft E T → sub E bot T
  | sub_arr : ∀ E S1 S2 T1 T2, sub E S1 T1 → sub E T2 S2 → sub E (arr S1 S2) (arr T1 T2)
  | sub_all : ∀ E S1 S2 T1 T2, sub E S1 T1 → (∀ X, sub E S2 T2) → sub E (all S1 S2) (all T1 T2)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:225-252
inductive typing : env → trm → typ → Prop :=
  | typing_var : ∀ E x T, List.lookup x E = some (bind.typ T) → typing E (var (Nat.ofString x)) T
  | typing_app : ∀ E e1 e2 T1 T2, typing E e1 (arr T1 T2) → typing E e2 T1 → typing E (app e1 e2) T2
  | typing_abs : ∀ E e T1 T2, (∀ x, typing ((x, bind.typ T1) :: E) e T2) → sub E T1 top → typing E (abs T1 e) (arr T1 T2)
  | typing_tabs : ∀ E e T1 T2, (∀ X, typing ((X, bind.sub T1 T1) :: E) e T2) → sub E T1 top → typing E (tabs T1 e) (all T1 T2)
| typing_tapp : ∀ E e T1 T2, typing E e (all T1 T2) → wft E T1 → typing E (tapp e T1) (open_tt T2 T1)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:254-260
inductive value : trm → Prop :=
  | val_abs : ∀ T e, value (abs T e)
  | val_tabs : ∀ T e, value (tabs T e)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:262-284
inductive red : trm → trm → Prop :=
  | red_app_abs : ∀ e1 e2 v2 T, value v2 → red (app (abs T e1) v2) (open_ee e1 v2)
  | red_app1 : ∀ e1 e1' e2, red e1 e1' → red (app e1 e2) (app e1' e2)
  | red_app2 : ∀ v1 e2 e2', value v1 → red e2 e2' → red (app v1 e2) (app v1 e2')
  | red_tapp_tabs : ∀ e T U, red (tapp (tabs T e) U) (open_te e U)
  | red_tapp : ∀ e e' T, red e e' → red (tapp e T) (tapp e' T)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:286-291
def preservation := ∀ e e' T, typing [] e T → red e e' → typing [] e' T

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:291-291
def progress := ∀ e T, typing [] e T → value e ∨ (∃ e', red e e')

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:305-315
def fv_tt (T : typ) : Finset String :=
  match T with
  | top => ∅
  | bot => ∅
  | arr T1 T2 => fv_tt T1 ∪ fv_tt T2
  | all T1 T2 => fv_tt T1 ∪ fv_tt T2

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:317-327
def fv_te (e : trm) : Finset String :=
  match e with
  | var n => {Nat.toString n}
  | app e1 e2 => fv_te e1 ∪ fv_te e2
  | abs T e1 => fv_tt T ∪ fv_te e1
  | tabs T e1 => fv_tt T ∪ fv_te e1
  | tapp e1 T => fv_te e1 ∪ fv_tt T

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:329-339
def fv_ee (e : trm) : Finset String :=
  match e with
  | var n => {Nat.toString n}
  | app e1 e2 => fv_ee e1 ∪ fv_ee e2
  | abs T e1 => fv_ee e1
  | tabs T e1 => fv_ee e1
  | tapp e1 T => fv_ee e1

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:341-351
def subst_tt (Z : String) (U : typ) (T : typ) : typ :=
  match T with
  | top => top
  | bot => bot
  | arr T1 T2 => arr (subst_tt Z U T1) (subst_tt Z U T2)
  | all T1 T2 => all (subst_tt Z U T1) (subst_tt Z U T2)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:353-363
def subst_te (Z : String) (U : typ) (e : trm) : trm :=
  match e with
  | var n => if Nat.toString n == Z then (tapp (var 0) U) else (var n)
  | app e1 e2 => app (subst_te Z U e1) (subst_te Z U e2)
  | abs T e1 => abs (subst_tt Z U T) (subst_te Z U e1)
  | tabs T e1 => tabs (subst_tt Z U T) (subst_te Z U e1)
  | tapp e1 T => tapp (subst_te Z U e1) (subst_tt Z U T)

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:365-375
def subst_ee (z : String) (u : trm) (e : trm) : trm :=
  match e with
  | var n => if Nat.toString n == z then u else (var n)
  | app e1 e2 => app (subst_ee z u e1) (subst_ee z u e2)
  | abs T e1 => abs T (subst_ee z u e1)
  | tabs T e1 => tabs T (subst_ee z u e1)
  | tapp e1 T => tapp (subst_ee z u e1) T

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:377-380
def subst_tb (Z : String) (P : typ) (b : bind) : bind :=
  match b with
  | bind.sub T1 T2 => bind.sub (subst_tt Z P T1) (subst_tt Z P T2)
  | bind.typ T => bind.typ (subst_tt Z P T)

import Lp2lc.Active.FsubL_alt

set_option autoImplicit true

open scoped Classical
