/-****************************************************************************
* Ddia (DOT-style calculus) – Definitions (scaffold from Coq Lp2lc_coq/Active/Ddia.v)
* This file contains only syntax, opening, fv, substitution, and judgments.
* All theorems/lemmas are placed in Proof.lean as sorry stubs for now.
*****************************************************************************-/

import Std
import Mathlib.Data.Finset.Basic
import Aesop
import «Lp2lc».Active.Shared

open Lp2lc.Active

namespace Lp2lc.Active.Ddia

/- Coq lines 23–41: Pre-types and pre-terms (mutual) -/

mutual
  inductive typ : Type where
    | typ_bot   : typ                      -- Coq: typ_bot
    | typ_top   : typ                      -- Coq: typ_top
    | typ_and   : typ → typ → typ          -- Coq: typ_and T1 T2
    | typ_or    : typ → typ → typ          -- Coq: typ_or T1 T2
    | typ_sel   : trm → typ                -- Coq: typ_sel t
    | typ_mem   : typ → typ → typ          -- Coq: typ_mem T1 T2
    | typ_all   : typ → typ → typ          -- Coq: typ_all T1 T2
  
  inductive trm : Type where
    | trm_bvar : Nat → trm                 -- Coq: trm_bvar i
    | trm_fvar : Var → trm                 -- Coq: trm_fvar x
    | trm_abs  : typ → trm → trm           -- Coq: trm_abs V e1
    | trm_mem  : typ → trm                 -- Coq: trm_mem T
    | trm_app  : trm → trm → trm           -- Coq: trm_app e1 e2
end

open typ trm

/- Coq lines 43–63: Opening operations (mutual) -/
mutual
  def open_t_rec (k : Nat) (f : trm) (T : typ) : typ :=
    match T with
    | typ_bot         => typ_bot
    | typ_top         => typ_top
    | typ_and T1 T2   => typ_and (open_t_rec k f T1) (open_t_rec k f T2)
    | typ_or  T1 T2   => typ_or  (open_t_rec k f T1) (open_t_rec k f T2)
    | typ_sel t       => typ_sel (open_e_rec k f t)
    | typ_mem T1 T2   => typ_mem (open_t_rec k f T1) (open_t_rec k f T2)
    | typ_all T1 T2   => typ_all (open_t_rec k f T1) (open_t_rec (k + 1) f T2)

  def open_e_rec (k : Nat) (f : trm) (e : trm) : trm :=
    match e with
    | trm_bvar i    => if k = i then f else trm_bvar i
    | trm_fvar x    => trm_fvar x
    | trm_abs V e1  => trm_abs (open_t_rec k f V) (open_e_rec (k + 1) f e1)
    | trm_mem T     => trm_mem (open_t_rec k f T)
    | trm_app e1 e2 => trm_app (open_e_rec k f e1) (open_e_rec k f e2)
end

/- Coq lines 65–67: Wrappers -/
@[simp] def open_t (T : typ) (f : trm) : typ := open_t_rec 0 f T
@[simp] def open_e (t : trm) (u : trm) : trm := open_e_rec 0 u t

/- Coq lines 70–72: Notations for opening with variables -/
notation:67 T " open_t_var " x => open_t T (trm.trm_fvar x)
notation:67 t " open_e_var " x => open_e t (trm.trm_fvar x)

/- Coq lines 75–115: Locally closed types/terms -/
mutual
  inductive def_type : typ → Prop where
    | type_bot :
        def_type typ_bot
    | type_top :
        def_type typ_top
    | type_and : ∀ {T1 T2},
        def_type T1 → def_type T2 → def_type (typ_and T1 T2)
    | type_or  : ∀ {T1 T2},
        def_type T1 → def_type T2 → def_type (typ_or T1 T2)
    | type_sel : ∀ {e1},
        def_term e1 → def_type (typ_sel e1)
    | type_mem : ∀ {T1 T2},
        def_type T1 → def_type T2 → def_type (typ_mem T1 T2)
    | type_all : ∀ (L : Vars) {T1 T2},
        def_type T1 → (∀ x, x ∉ L → def_type (open_t T2 (trm.trm_fvar x))) →
        def_type (typ_all T1 T2)
  
  inductive def_term : trm → Prop where
    | term_var : ∀ {x : Var}, def_term (trm_fvar x)
    | term_abs : ∀ (L : Vars) {V e1},
        def_type V → (∀ x, x ∉ L → def_term (open_e e1 (trm.trm_fvar x))) →
        def_term (trm_abs V e1)
    | term_mem : ∀ {T1},
        def_type T1 → def_term (trm_mem T1)
    | term_app : ∀ {e1 e2},
        def_term e1 → def_term e2 → def_term (trm_app e1 e2)
end

/- Coq lines 119–127: Values -/
inductive value : trm → Prop where
  | value_abs  : ∀ {V e1}, def_term (trm_abs V e1) → value (trm_abs V e1)
  | value_mem  : ∀ {V},    def_term (trm_mem V)    → value (trm_mem V)

/- Coq lines 127–128: Environments -/
abbrev env := List (Var × typ)

/- Utilities consistent with Shared.Env -/
@[simp] def dom (E : env) : Vars := Env.domOf E
@[simp] def binds (x : Var) (T : typ) (E : env) : Prop := E.lookup x = some T

-- bring abstract ok into scope (mirrors LibEnv.ok signature)
-- use shared ok from Lp2lc.Active.Shared

/- Coq lines 134–175: Well-formedness of types/terms in env -/
mutual
  inductive wft : env → typ → Prop where
    | wft_bot : ∀ {E}, wft E typ_bot
    | wft_top : ∀ {E}, wft E typ_top
    | wft_and : ∀ {E T1 T2}, wft E T1 → wft E T2 → wft E (typ_and T1 T2)
    | wft_or  : ∀ {E T1 T2}, wft E T1 → wft E T2 → wft E (typ_or T1 T2)
    | wft_sel : ∀ {E e}, (value e ∨ ∃ x, trm_fvar x = e) → wfe E e → wft E (typ_sel e)
    | wft_mem : ∀ {E T1 T2}, wft E T1 → wft E T2 → wft E (typ_mem T1 T2)
    | wft_all : ∀ (L : Vars) {E T1 T2},
        wft E T1 → (∀ x, x ∉ L → wft ((x, T1) :: E) (open_t T2 (trm.trm_fvar x))) →
        wft E (typ_all T1 T2)
  
  inductive wfe : env → trm → Prop where
    | wfe_var : ∀ {U E x}, binds x U E → wfe E (trm_fvar x)
    | wfe_abs : ∀ (L : Vars) {E V e},
        wft E V → (∀ x, x ∉ L → wfe ((x, V) :: E) (open_e e (trm.trm_fvar x))) →
        wfe E (trm_abs V e)
    | wfe_mem : ∀ {E T}, wft E T → wfe E (trm_mem T)
    | wfe_app : ∀ {E e1 e2}, wfe E e1 → wfe E e2 → wfe E (trm_app e1 e2)
end

/- Coq lines 181–186: Well-formed environment (no duplicates, each type wft) -/
inductive okt : env → Prop where
  | okt_empty : okt []
  | okt_push  : ∀ {E x T}, okt E → wft E T → E.lookup x = none → okt ((x, T) :: E)

/- Coq lines 189–260: Subtyping and has -/
mutual
  inductive sub : env → typ → typ → Prop where
    | sub_bot : ∀ {E T}, okt E → wft E T → sub E typ_bot T
    | sub_top : ∀ {E S}, okt E → wft E S → sub E S typ_top
    | sub_and11 : ∀ {E T1 T2 T}, wft E T2 → sub E T1 T → sub E (typ_and T1 T2) T
    | sub_and12 : ∀ {E T1 T2 T}, wft E T1 → sub E T2 T → sub E (typ_and T1 T2) T
    | sub_and2  : ∀ {E T T1 T2}, sub E T T1 → sub E T T2 → sub E T (typ_and T1 T2)
    | sub_or21  : ∀ {E T T1 T2}, wft E T2 → sub E T T1 → sub E T (typ_or T1 T2)
    | sub_or22  : ∀ {E T T1 T2}, wft E T1 → sub E T T2 → sub E T (typ_or T1 T2)
    | sub_or1   : ∀ {E T1 T2 T}, sub E T1 T → sub E T2 T → sub E (typ_or T1 T2) T
    | sub_refl_sel : ∀ {E t}, okt E → wft E (typ_sel t) → sub E (typ_sel t) (typ_sel t)
    | sub_sel1 : ∀ {E S U t}, has E t (typ_mem S U) → sub E (typ_sel t) U
    | sub_sel2 : ∀ {E S U t}, has E t (typ_mem S U) → sub E S (typ_sel t)
    | sub_mem : ∀ {E S1 U1 S2 U2}, sub E S2 S1 → sub E U1 U2 → sub E (typ_mem S1 U1) (typ_mem S2 U2)
    | sub_all : ∀ (L : Vars) {E S1 S2 T1 T2},
        sub E T1 S1 → (∀ x, x ∉ L → sub ((x, T1) :: E) (open_t S2 (trm.trm_fvar x)) (open_t T2 (trm.trm_fvar x))) →
        sub E (typ_all S1 S2) (typ_all T1 T2)
    | sub_trans : ∀ {E S T U}, sub E S T → sub E T U → sub E S U
  
  inductive has : env → trm → typ → Prop where
    | has_var : ∀ {E x T}, okt E → binds x T E → has E (trm_fvar x) T
    | has_mem : ∀ {E T}, okt E → wft E T → has E (trm_mem T) (typ_mem T T)
    | has_abs : ∀ {E V e T}, okt E → wfe E (trm_abs V e) → wft E (typ_all V T) → has E (trm_abs V e) (typ_all V T)
    | has_sub : ∀ {E t T U}, has E t T → sub E T U → has E t U
end

/- Coq lines 262–292: Typing -/
inductive typing : env → trm → typ → Prop where
  | typing_var : ∀ {E x T}, okt E → binds x T E → typing E (trm.trm_fvar x) T
  | typing_abs : ∀ (L : Vars) {E V e1 T1},
      (∀ x, x ∉ L → typing ((x, V) :: E) (open_e e1 (trm.trm_fvar x)) (open_t T1 (trm.trm_fvar x))) →
      typing E (trm.trm_abs V e1) (typ.typ_all V T1)
  | typing_mem : ∀ {E T1}, okt E → wft E T1 → typing E (trm.trm_mem T1) (typ.typ_mem T1 T1)
  | typing_app : ∀ {T1 E e1 e2 T2}, typing E e1 (typ.typ_all T1 T2) → typing E e2 T1 → wft E T2 → typing E (trm.trm_app e1 e2) T2
  | typing_appvar : ∀ {T1 E e1 e2 T2 T2' M},
      typing E e1 (typ.typ_all T1 T2) → typing E e2 T1 → has E e2 M →
      T2' = open_t T2 e2 → wft E T2' → typing E (trm.trm_app e1 e2) T2'
  | typing_sub : ∀ {S E e T}, typing E e S → sub E S T → typing E e T

/- Coq lines 296–309: One-step reduction -/
inductive red : trm → trm → Prop where
  | red_app_1 : ∀ {e1 e1' e2}, def_term e2 → red e1 e1' → red (trm.trm_app e1 e2) (trm.trm_app e1' e2)
  | red_app_2 : ∀ {e1 e2 e2'}, value e1 → red e2 e2' → red (trm.trm_app e1 e2) (trm.trm_app e1 e2')
  | red_abs : ∀ {V e1 v2}, def_term (trm.trm_abs V e1) → value v2 → red (trm.trm_app (trm.trm_abs V e1) v2) (open_e e1 v2)

/- Coq lines 312–321: Preservation and Progress statements -/
@[simp] def preservation : Prop := ∀ (e e' : trm) (T : typ), typing [] e T → red e e' → typing [] e' T
@[simp] def progress : Prop := ∀ (e : trm) (T : typ), typing [] e T → value e ∨ ∃ e', red e e'

/- Coq lines 329–351: Free variables (mutual) -/
mutual
  def fv_t (T : typ) : Vars :=
    match T with
    | typ_bot         => ∅
    | typ_top         => ∅
    | typ_and T1 T2   => (fv_t T1) ∪ (fv_t T2)
    | typ_or  T1 T2   => (fv_t T1) ∪ (fv_t T2)
    | typ_sel t       => fv_e t
    | typ_mem T1 T2   => (fv_t T1) ∪ (fv_t T2)
    | typ_all T1 T2   => (fv_t T1) ∪ (fv_t T2)
  
  def fv_e (e : trm) : Vars :=
    match e with
    | trm_bvar _      => ∅
    | trm_fvar x      => {x}
    | trm_abs V e1    => (fv_t V) ∪ (fv_e e1)
    | trm_mem T       => fv_t T
    | trm_app e1 e2   => (fv_e e1) ∪ (fv_e e2)
end

/- Coq lines 355–375: Substitutions (mutual) -/
mutual
  def subst_t (Z : Var) (u : trm) (T : typ) : typ :=
    match T with
    | typ_bot         => typ_bot
    | typ_top         => typ_top
    | typ_and T1 T2   => typ_and (subst_t Z u T1) (subst_t Z u T2)
    | typ_or  T1 T2   => typ_or  (subst_t Z u T1) (subst_t Z u T2)
    | typ_sel t       => typ_sel (subst_e Z u t)
    | typ_mem T1 T2   => typ_mem (subst_t Z u T1) (subst_t Z u T2)
    | typ_all T1 T2   => typ_all (subst_t Z u T1) (subst_t Z u T2)

  def subst_e (Z : Var) (u : trm) (e : trm) : trm :=
    match e with
    | trm_bvar i      => trm_bvar i
    | trm_fvar x      => by
        classical
        exact (if h : x = Z then (by simpa [h] using u) else trm_fvar x)
    | trm_abs V e1    => trm_abs (subst_t Z u V) (subst_e Z u e1)
    | trm_mem T1      => trm_mem (subst_t Z u T1)
    | trm_app e1 e2   => trm_app (subst_e Z u e1) (subst_e Z u e2)
end

/- Map substitution over environments (used later in proofs) -/
@[simp] def map_subst_t (Z : Var) (u : trm) (E : env) : env :=
  Env.mapSecond (subst_t Z u) E

/- Additional small-step pseudo-subtyping and possible types (Coq lines ~1491, ~1575) -/
inductive psub : typ → typ → Prop where
  | psub_bot : ∀ {U}, wft [] U → psub typ.typ_bot U
  | psub_top : ∀ {S}, wft [] S → psub S typ.typ_top
  | psub_and11 : ∀ {T1 T2 T}, wft [] T2 → psub T1 T → psub (typ.typ_and T1 T2) T
  | psub_and12 : ∀ {T1 T2 T}, wft [] T1 → psub T2 T → psub (typ.typ_and T1 T2) T
  | psub_and2 : ∀ {T T1 T2}, psub T T1 → psub T T2 → psub T (typ.typ_and T1 T2)
  | psub_or21 : ∀ {T T1 T2}, wft [] T2 → psub T T1 → psub T (typ.typ_or T1 T2)
  | psub_or22 : ∀ {T T1 T2}, wft [] T1 → psub T T2 → psub T (typ.typ_or T1 T2)
  | psub_or1 : ∀ {T1 T2 T}, psub T1 T → psub T2 T → psub (typ.typ_or T1 T2) T
  | psub_refl_sel : ∀ {t}, wft [] (typ.typ_sel t) → psub (typ.typ_sel t) (typ.typ_sel t)
  | psub_sel1 : ∀ {U}, wft [] U → psub (typ.typ_sel (trm.trm_mem U)) U
  | psub_sel2 : ∀ {S}, wft [] S → psub S (typ.typ_sel (trm.trm_mem S))
  | psub_mem : ∀ {S1 U1 S2 U2}, psub S2 S1 → psub U1 U2 → psub (typ.typ_mem S1 U1) (typ.typ_mem S2 U2)
  | psub_all : ∀ (L : Vars) {S1 S2 T1 T2},
      psub T1 S1 →
      (∀ x, x ∉ L → sub ((x, T1) :: []) (open_t S2 (trm.trm_fvar x)) (open_t T2 (trm.trm_fvar x))) →
      psub (typ.typ_all S1 S2) (typ.typ_all T1 T2)
  | psub_trans : ∀ {S T U}, psub S T → psub T U → psub S U

inductive possible_types : Nat → trm → typ → Prop where
  | pt_top : ∀ {n v}, value v → wfe [] v → possible_types n v typ.typ_top
  | pt_mem : ∀ {n T S U}, psub S T → psub T U → possible_types n (trm.trm_mem T) (typ.typ_mem S U)
  | pt_all : ∀ (L : Vars) {n V V' e1 T1 T1'},
      (∀ X, X ∉ L → typing ((X, V) :: []) (open_e e1 (trm.trm_fvar X)) (open_t T1 (trm.trm_fvar X))) →
      psub V' V →
      (∀ X, X ∉ L → sub ((X, V') :: []) (open_t T1 (trm.trm_fvar X)) (open_t T1' (trm.trm_fvar X))) →
      possible_types (Nat.succ n) (trm.trm_abs V e1) (typ.typ_all V' T1')
  | pt_all_shallow : ∀ {V V' e1 T1'},
      wfe [] (trm.trm_abs V e1) → wft [] (typ.typ_all V' T1') →
      possible_types 0 (trm.trm_abs V e1) (typ.typ_all V' T1')
  | pt_sel : ∀ {n v S}, possible_types n v S → possible_types n v (typ.typ_sel (trm.trm_mem S))
  | pt_and : ∀ {n v T1 T2}, possible_types n v T1 → possible_types n v T2 → possible_types n v (typ.typ_and T1 T2)
  | pt_or1 : ∀ {n v T1 T2}, possible_types n v T1 → wft [] T2 → possible_types n v (typ.typ_or T1 T2)
  | pt_or2 : ∀ {n v T1 T2}, possible_types n v T2 → wft [] T1 → possible_types n v (typ.typ_or T1 T2)

end Lp2lc.Active.Ddia
