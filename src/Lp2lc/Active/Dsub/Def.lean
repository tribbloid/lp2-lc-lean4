
namespace Lp2lc.Active.Dsub

-- Coq: Lp2lc_coq\Active\Dsub.v:24-37
inductive typ : Type :=
  | top : typ
  | arr : typ → typ → typ
  | all : trm → typ → typ

-- Coq: Lp2lc_coq\Active\Dsub.v:24-37
inductive trm : Type :=
  | var : Nat → trm
  | app : trm → trm → trm
  | abs : typ → trm → trm
  | tabs : trm → trm → trm
| tapp : trm → trm → trm

-- Coq: Lp2lc_coq\Active\Dsub.v:39-56
def open_t_rec (k : Nat) (f : trm) (T : typ) : typ :=
  match T with
  | top => top
  | arr T1 T2 => arr (open_t_rec k f T1) (open_t_rec k f T2)
  | all e T2 => all (open_e_rec k f e) (open_t_rec (k + 1) f T2)

-- Coq: Lp2lc_coq\Active\Dsub.v:58-58
def open_t (T : typ) (f : trm) : typ := open_t_rec 0 f T

-- Coq: Lp2lc_coq\Active\Dsub.v:59-59
def open_e (t u : trm) : trm := open_e_rec 0 u t

-- Coq: Lp2lc_coq\Active\Dsub.v:68-99
inductive type : typ → Prop :=
  | type_top : type top
  | type_arr : ∀ T1 T2, type T1 → type T2 → type (arr T1 T2)
  | type_all : ∀ e T, term e → (∀ x, type T) → type (all e T)

-- Coq: Lp2lc_coq\Active\Dsub.v:101-107
inductive value : trm → Prop :=
  | val_abs : ∀ T e, value (abs T e)
  | val_tabs : ∀ T e, value (tabs T e)

-- Coq: Lp2lc_coq\Active\Dsub.v:109-109
def env := List (String × typ)

-- Coq: Lp2lc_coq\Active\Dsub.v:116-150
inductive wft : env → typ → Prop :=
  | wft_top : ∀ E, wft E top
  | wft_arr : ∀ E T1 T2, wft E T1 → wft E T2 → wft E (arr T1 T2)
  | wft_all : ∀ E e T, wfe E e → (∀ x, wft (E ++ [(x, T)]) T) → wft E (all e T)

-- Coq: Lp2lc_coq\Active\Dsub.v:152-158
inductive okt : env → Prop :=
  | okt_empty : okt []
  | okt_push : ∀ E x T, okt E → (x ∉ E.keys) → wft E T → okt ((x, T) :: E)

-- Coq: Lp2lc_coq\Active\Dsub.v:160-208
inductive sub : env → typ → typ → Prop :=
  | sub_refl : ∀ E T, wft E T → sub E T T
  | sub_top : ∀ E T, wft E T → sub E T top
  | sub_arr : ∀ E S1 S2 T1 T2, sub E S1 T1 → sub E T2 S2 → sub E (arr S1 S2) (arr T1 T2)
  | sub_all : ∀ E e S T, sub E S T → (∀ x, sub (E ++ [(x, T)]) S T) → sub E (all e S) (all e T)
  | sub_trans : ∀ E S T U, sub E S T → sub E T U → sub E S U

-- Coq: Lp2lc_coq\Active\Dsub.v:210-240
inductive typing : env → trm → typ → Prop :=
  | typing_var : ∀ E x T, List.lookup x E = some T → typing E (var (Nat.ofString x)) T
  | typing_app : ∀ E e1 e2 T1 T2, typing E e1 (arr T1 T2) → typing E e2 T1 → typing E (app e1 e2) T2
  | typing_abs : ∀ E e T1 T2, (∀ x, typing ((x, T1) :: E) e T2) → sub E T1 top → typing E (abs T1 e) (arr T1 T2)
  | typing_tabs : ∀ E e T, (∀ x, typing ((x, T) :: E) e T) → sub E T top → typing E (tabs e) (all e T)
| typing_tapp : ∀ E e1 e2 T1, typing E e1 (all e2 T1) → typing E e2 (all e2 T1) → typing E (tapp e1 e2) (open_t T1 e2)

-- Coq: Lp2lc_coq\Active\Dsub.v:242-256
inductive red : trm → trm → Prop :=
  | red_app_abs : ∀ e1 e2 v2 T, value v2 → red (app (abs T e1) v2) (open_e e1 v2)
  | red_app1 : ∀ e1 e1' e2, red e1 e1' → red (app e1 e2) (app e1' e2)
  | red_app2 : ∀ v1 e2 e2', value v1 → red e2 e2' → red (app v1 e2) (app v1 e2')
  | red_tapp : ∀ e1 e1' e2, red e1 e1' → red (tapp e1 e2) (tapp e1' e2)

-- Coq: Lp2lc_coq\Active\Dsub.v:258-263
def preservation := ∀ e e' T, typing [] e T → red e e' → typing [] e' T

-- Coq: Lp2lc_coq\Active\Dsub.v:263-263
def progress := ∀ e T, typing [] e T → value e ∨ (∃ e', red e e')

-- Coq: Lp2lc_coq\Active\Dsub.v:277-296
def fv_t (T : typ) : Finset String :=
  match T with
  | top => ∅
  | arr T1 T2 => fv_t T1 ∪ fv_t T2
  | all e T2 => fv_ee e ∪ fv_t T2

def fv_ee (e : trm) : Finset String :=
  match e with
  | var n => {Nat.toString n}
  | app e1 e2 => fv_ee e1 ∪ fv_ee e2
  | abs T e1 => fv_ee e1
  | tabs T e1 => fv_ee e1
  | tapp e1 T => fv_ee e1

-- Coq: Lp2lc_coq\Active\Dsub.v:298-316
def subst_t (z : String) (u : trm) (T : typ) : typ :=
  match T with
  | top => top
  | arr T1 T2 => arr (subst_t z u T1) (subst_t z u T2)
  | all e T2 => all (subst_e z u e) (subst_t z u T2)

def subst_e (z : String) (u : trm) (e : trm) : trm :=
  match e with
  | var n => if Nat.toString n == z then u else (var n)
  | app e1 e2 => app (subst_e z u e1) (subst_e z u e2)
  | abs T e1 => abs T (subst_e z u e1)
  | tabs e1 => tabs (subst_e z u e1)
  | tapp e1 e2 => tapp (subst_e z u e1) e2

import Lp2lc.Active.Dsub

set_option autoImplicit true

open scoped Classical
