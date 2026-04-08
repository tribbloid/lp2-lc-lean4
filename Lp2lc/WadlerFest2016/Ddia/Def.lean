/-****************************************************************************
* Ddia (DOT-style calculus) – Definitions (scaffold from Coq Lp2lc_coq/Active/Ddia.v)
* This file contains only syntax, opening, fv, substitution, and judgments.
* All theorems/lemmas are placed in Proof.lean as sorry stubs for now.
*****************************************************************************-/

import Std
import Mathlib.Data.Finset.Basic
import Aesop
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Ddia

/- Coq lines 23–41: Pre-types and pre-terms (mutual) -/

mutual
  inductive Typ : Type where
    | typ_bot   : Typ                      -- Coq: typ_bot
    | typ_top   : Typ                      -- Coq: typ_top
    | typ_and   : Typ → Typ → Typ          -- Coq: typ_and T1 T2
    | typ_or    : Typ → Typ → Typ          -- Coq: typ_or T1 T2
    | typ_sel   : Trm → Typ                -- Coq: typ_sel t
    | typ_mem   : Typ → Typ → Typ          -- Coq: typ_mem T1 T2
    | typ_all   : Typ → Typ → Typ          -- Coq: typ_all T1 T2
  
  inductive Trm : Type where
    | trm_bvar : Nat → Trm                 -- Coq: trm_bvar i
    | trm_fvar : Var → Trm                 -- Coq: trm_fvar x
    | trm_abs  : Typ → Trm → Trm           -- Coq: trm_abs V e1
    | trm_mem  : Typ → Trm                 -- Coq: trm_mem T
    | trm_app  : Trm → Trm → Trm           -- Coq: trm_app e1 e2
end

open Typ Trm

/- Coq lines 43–63: Opening operations (mutual) -/
mutual
  def open_t_rec (k : Nat) (f : Trm) (T : Typ) : Typ :=
    match T with
    | typ_bot         => typ_bot
    | typ_top         => typ_top
    | typ_and T1 T2   => typ_and (open_t_rec k f T1) (open_t_rec k f T2)
    | typ_or  T1 T2   => typ_or  (open_t_rec k f T1) (open_t_rec k f T2)
    | typ_sel t       => typ_sel (open_e_rec k f t)
    | typ_mem T1 T2   => typ_mem (open_t_rec k f T1) (open_t_rec k f T2)
    | typ_all T1 T2   => typ_all (open_t_rec k f T1) (open_t_rec (k + 1) f T2)

  def open_e_rec (k : Nat) (f : Trm) (e : Trm) : Trm :=
    match e with
    | trm_bvar i    => if k = i then f else trm_bvar i
    | trm_fvar x    => trm_fvar x
    | trm_abs V e1  => trm_abs (open_t_rec k f V) (open_e_rec (k + 1) f e1)
    | trm_mem T     => trm_mem (open_t_rec k f T)
    | trm_app e1 e2 => trm_app (open_e_rec k f e1) (open_e_rec k f e2)
end

/- Coq lines 65–67: Wrappers -/
@[simp] def open_t (T : Typ) (f : Trm) : Typ := open_t_rec 0 f T
@[simp] def open_e (t : Trm) (u : Trm) : Trm := open_e_rec 0 u t

/- Coq lines 70–72: Notations for opening with variables -/
notation:67 T " open_t_var " x => open_t T (Trm.trm_fvar x)
notation:67 t " open_e_var " x => open_e t (Trm.trm_fvar x)

/- Coq lines 75–115: Locally closed types/terms -/
mutual
  inductive DefType : Typ → Prop where
    | type_bot :
        DefType typ_bot
    | type_top :
        DefType typ_top
    | type_and : ∀ {T1 T2},
        DefType T1 → DefType T2 → DefType (typ_and T1 T2)
    | type_or  : ∀ {T1 T2},
        DefType T1 → DefType T2 → DefType (typ_or T1 T2)
    | type_sel : ∀ {e1},
        DefTerm e1 → DefType (typ_sel e1)
    | type_mem : ∀ {T1 T2},
        DefType T1 → DefType T2 → DefType (typ_mem T1 T2)
    | type_all : ∀ (L : Vars) {T1 T2},
        DefType T1 → (∀ x, x ∉ L → DefType (open_t T2 (Trm.trm_fvar x))) →
        DefType (typ_all T1 T2)
  
  inductive DefTerm : Trm → Prop where
    | term_var : ∀ {x : Var}, DefTerm (trm_fvar x)
    | term_abs : ∀ (L : Vars) {V e1},
        DefType V → (∀ x, x ∉ L → DefTerm (open_e e1 (Trm.trm_fvar x))) →
        DefTerm (trm_abs V e1)
    | term_mem : ∀ {T1},
        DefType T1 → DefTerm (trm_mem T1)
    | term_app : ∀ {e1 e2},
        DefTerm e1 → DefTerm e2 → DefTerm (trm_app e1 e2)
end

/- Coq lines 119–127: Values -/
inductive Value : Trm → Prop where
  | value_abs  : ∀ {V e1}, DefTerm (trm_abs V e1) → Value (trm_abs V e1)
  | value_mem  : ∀ {V},    DefTerm (trm_mem V)    → Value (trm_mem V)

/- Coq lines 127–128: Environments -/
abbrev Env := List (Var × Typ)

/- Utilities consistent with Shared.Env -/
@[simp] def dom (E : Env) : Vars := Env.domOf E
@[simp] def binds (x : Var) (T : Typ) (E : Env) : Prop := E.lookup x = some T

-- bring abstract ok into scope (mirrors LibEnv.ok signature)
-- use shared ok from Lp2lc.Active.Shared

/- Coq lines 134–175: Well-formedness of types/terms in Env -/
mutual
  inductive Wft : Env → Typ → Prop where
    | wft_bot : ∀ {E}, Wft E typ_bot
    | wft_top : ∀ {E}, Wft E typ_top
    | wft_and : ∀ {E T1 T2}, Wft E T1 → Wft E T2 → Wft E (typ_and T1 T2)
    | wft_or  : ∀ {E T1 T2}, Wft E T1 → Wft E T2 → Wft E (typ_or T1 T2)
    | wft_sel : ∀ {E e}, (Value e ∨ ∃ x, trm_fvar x = e) → Wfe E e → Wft E (typ_sel e)
    | wft_mem : ∀ {E T1 T2}, Wft E T1 → Wft E T2 → Wft E (typ_mem T1 T2)
    | wft_all : ∀ (L : Vars) {E T1 T2},
        Wft E T1 → (∀ x, x ∉ L → Wft ((x, T1) :: E) (open_t T2 (Trm.trm_fvar x))) →
        Wft E (typ_all T1 T2)
  
  inductive Wfe : Env → Trm → Prop where
    | wfe_var : ∀ {U E x}, binds x U E → Wfe E (trm_fvar x)
    | wfe_abs : ∀ (L : Vars) {E V e},
        Wft E V → (∀ x, x ∉ L → Wfe ((x, V) :: E) (open_e e (Trm.trm_fvar x))) →
        Wfe E (trm_abs V e)
    | wfe_mem : ∀ {E T}, Wft E T → Wfe E (trm_mem T)
    | wfe_app : ∀ {E e1 e2}, Wfe E e1 → Wfe E e2 → Wfe E (trm_app e1 e2)
end

/- Coq lines 181–186: Well-formed environment (no duplicates, each type Wft) -/
inductive Okt : Env → Prop where
  | okt_empty : Okt []
  | okt_push  : ∀ {E x T}, Okt E → Wft E T → E.lookup x = none → Okt ((x, T) :: E)

/- Coq lines 189–260: Subtyping and Has -/
mutual
  inductive Sub : Env → Typ → Typ → Prop where
    | sub_bot : ∀ {E T}, Okt E → Wft E T → Sub E typ_bot T
    | sub_top : ∀ {E S}, Okt E → Wft E S → Sub E S typ_top
    | sub_and11 : ∀ {E T1 T2 T}, Wft E T2 → Sub E T1 T → Sub E (typ_and T1 T2) T
    | sub_and12 : ∀ {E T1 T2 T}, Wft E T1 → Sub E T2 T → Sub E (typ_and T1 T2) T
    | sub_and2  : ∀ {E T T1 T2}, Sub E T T1 → Sub E T T2 → Sub E T (typ_and T1 T2)
    | sub_or21  : ∀ {E T T1 T2}, Wft E T2 → Sub E T T1 → Sub E T (typ_or T1 T2)
    | sub_or22  : ∀ {E T T1 T2}, Wft E T1 → Sub E T T2 → Sub E T (typ_or T1 T2)
    | sub_or1   : ∀ {E T1 T2 T}, Sub E T1 T → Sub E T2 T → Sub E (typ_or T1 T2) T
    | sub_refl_sel : ∀ {E t}, Okt E → Wft E (typ_sel t) → Sub E (typ_sel t) (typ_sel t)
    | sub_sel1 : ∀ {E S U t}, Has E t (typ_mem S U) → Sub E (typ_sel t) U
    | sub_sel2 : ∀ {E S U t}, Has E t (typ_mem S U) → Sub E S (typ_sel t)
    | sub_mem : ∀ {E S1 U1 S2 U2}, Sub E S2 S1 → Sub E U1 U2 → Sub E (typ_mem S1 U1) (typ_mem S2 U2)
    | sub_all : ∀ (L : Vars) {E S1 S2 T1 T2},
        Sub E T1 S1 → (∀ x, x ∉ L → Sub ((x, T1) :: E) (open_t S2 (Trm.trm_fvar x)) (open_t T2 (Trm.trm_fvar x))) →
        Sub E (typ_all S1 S2) (typ_all T1 T2)
    | sub_trans : ∀ {E S T U}, Sub E S T → Sub E T U → Sub E S U
  
  inductive Has : Env → Trm → Typ → Prop where
    | has_var : ∀ {E x T}, Okt E → binds x T E → Has E (trm_fvar x) T
    | has_mem : ∀ {E T}, Okt E → Wft E T → Has E (trm_mem T) (typ_mem T T)
    | has_abs : ∀ {E V e T}, Okt E → Wfe E (trm_abs V e) → Wft E (typ_all V T) → Has E (trm_abs V e) (typ_all V T)
    | has_sub : ∀ {E t T U}, Has E t T → Sub E T U → Has E t U
end

/- Coq lines 262–292: Typing -/
inductive Typing : Env → Trm → Typ → Prop where
  | typing_var : ∀ {E x T}, Okt E → binds x T E → Typing E (Trm.trm_fvar x) T
  | typing_abs : ∀ (L : Vars) {E V e1 T1},
      (∀ x, x ∉ L → Typing ((x, V) :: E) (open_e e1 (Trm.trm_fvar x)) (open_t T1 (Trm.trm_fvar x))) →
      Typing E (Trm.trm_abs V e1) (Typ.typ_all V T1)
  | typing_mem : ∀ {E T1}, Okt E → Wft E T1 → Typing E (Trm.trm_mem T1) (Typ.typ_mem T1 T1)
  | typing_app : ∀ {T1 E e1 e2 T2}, Typing E e1 (Typ.typ_all T1 T2) → Typing E e2 T1 → Wft E T2 → Typing E (Trm.trm_app e1 e2) T2
  | typing_appvar : ∀ {T1 E e1 e2 T2 T2' M},
      Typing E e1 (Typ.typ_all T1 T2) → Typing E e2 T1 → Has E e2 M →
      T2' = open_t T2 e2 → Wft E T2' → Typing E (Trm.trm_app e1 e2) T2'
  | typing_sub : ∀ {S E e T}, Typing E e S → Sub E S T → Typing E e T

/- Coq lines 296–309: One-step reduction -/
inductive Red : Trm → Trm → Prop where
  | red_app_1 : ∀ {e1 e1' e2}, DefTerm e2 → Red e1 e1' → Red (Trm.trm_app e1 e2) (Trm.trm_app e1' e2)
  | red_app_2 : ∀ {e1 e2 e2'}, Value e1 → Red e2 e2' → Red (Trm.trm_app e1 e2) (Trm.trm_app e1 e2')
  | red_abs : ∀ {V e1 v2}, DefTerm (Trm.trm_abs V e1) → Value v2 → Red (Trm.trm_app (Trm.trm_abs V e1) v2) (open_e e1 v2)

/- Coq lines 312–321: Preservation and Progress statements -/
@[simp] def preservation : Prop := ∀ (e e' : Trm) (T : Typ), Typing [] e T → Red e e' → Typing [] e' T
@[simp] def progress : Prop := ∀ (e : Trm) (T : Typ), Typing [] e T → Value e ∨ ∃ e', Red e e'

/- Coq lines 329–351: Free variables (mutual) -/
mutual
  def fv_t (T : Typ) : Vars :=
    match T with
    | typ_bot         => ∅
    | typ_top         => ∅
    | typ_and T1 T2   => (fv_t T1) ∪ (fv_t T2)
    | typ_or  T1 T2   => (fv_t T1) ∪ (fv_t T2)
    | typ_sel t       => fv_e t
    | typ_mem T1 T2   => (fv_t T1) ∪ (fv_t T2)
    | typ_all T1 T2   => (fv_t T1) ∪ (fv_t T2)
  
  def fv_e (e : Trm) : Vars :=
    match e with
    | trm_bvar _      => ∅
    | trm_fvar x      => {x}
    | trm_abs V e1    => (fv_t V) ∪ (fv_e e1)
    | trm_mem T       => fv_t T
    | trm_app e1 e2   => (fv_e e1) ∪ (fv_e e2)
end

/- Coq lines 355–375: Substitutions (mutual) -/
mutual
  def subst_t (Z : Var) (u : Trm) (T : Typ) : Typ :=
    match T with
    | typ_bot         => typ_bot
    | typ_top         => typ_top
    | typ_and T1 T2   => typ_and (subst_t Z u T1) (subst_t Z u T2)
    | typ_or  T1 T2   => typ_or  (subst_t Z u T1) (subst_t Z u T2)
    | typ_sel t       => typ_sel (subst_e Z u t)
    | typ_mem T1 T2   => typ_mem (subst_t Z u T1) (subst_t Z u T2)
    | typ_all T1 T2   => typ_all (subst_t Z u T1) (subst_t Z u T2)

  def subst_e (Z : Var) (u : Trm) (e : Trm) : Trm :=
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
@[simp] def map_subst_t (Z : Var) (u : Trm) (E : Env) : Env :=
  Env.mapSecond (subst_t Z u) E

/- Additional small-step pseudo-subtyping and possible types (Coq lines ~1491, ~1575) -/
inductive Psub : Typ → Typ → Prop where
  | psub_bot : ∀ {U}, Wft [] U → Psub Typ.typ_bot U
  | psub_top : ∀ {S}, Wft [] S → Psub S Typ.typ_top
  | psub_and11 : ∀ {T1 T2 T}, Wft [] T2 → Psub T1 T → Psub (Typ.typ_and T1 T2) T
  | psub_and12 : ∀ {T1 T2 T}, Wft [] T1 → Psub T2 T → Psub (Typ.typ_and T1 T2) T
  | psub_and2 : ∀ {T T1 T2}, Psub T T1 → Psub T T2 → Psub T (Typ.typ_and T1 T2)
  | psub_or21 : ∀ {T T1 T2}, Wft [] T2 → Psub T T1 → Psub T (Typ.typ_or T1 T2)
  | psub_or22 : ∀ {T T1 T2}, Wft [] T1 → Psub T T2 → Psub T (Typ.typ_or T1 T2)
  | psub_or1 : ∀ {T1 T2 T}, Psub T1 T → Psub T2 T → Psub (Typ.typ_or T1 T2) T
  | psub_refl_sel : ∀ {t}, Wft [] (Typ.typ_sel t) → Psub (Typ.typ_sel t) (Typ.typ_sel t)
  | psub_sel1 : ∀ {U}, Wft [] U → Psub (Typ.typ_sel (Trm.trm_mem U)) U
  | psub_sel2 : ∀ {S}, Wft [] S → Psub S (Typ.typ_sel (Trm.trm_mem S))
  | psub_mem : ∀ {S1 U1 S2 U2}, Psub S2 S1 → Psub U1 U2 → Psub (Typ.typ_mem S1 U1) (Typ.typ_mem S2 U2)
  | psub_all : ∀ (L : Vars) {S1 S2 T1 T2},
      Psub T1 S1 →
      (∀ x, x ∉ L → Sub ((x, T1) :: []) (open_t S2 (Trm.trm_fvar x)) (open_t T2 (Trm.trm_fvar x))) →
      Psub (Typ.typ_all S1 S2) (Typ.typ_all T1 T2)
  | psub_trans : ∀ {S T U}, Psub S T → Psub T U → Psub S U

inductive PossibleTypes : Nat → Trm → Typ → Prop where
  | pt_top : ∀ {n v}, Value v → Wfe [] v → PossibleTypes n v Typ.typ_top
  | pt_mem : ∀ {n T S U}, Psub S T → Psub T U → PossibleTypes n (Trm.trm_mem T) (Typ.typ_mem S U)
  | pt_all : ∀ (L : Vars) {n V V' e1 T1 T1'},
      (∀ X, X ∉ L → Typing ((X, V) :: []) (open_e e1 (Trm.trm_fvar X)) (open_t T1 (Trm.trm_fvar X))) →
      Psub V' V →
      (∀ X, X ∉ L → Sub ((X, V') :: []) (open_t T1 (Trm.trm_fvar X)) (open_t T1' (Trm.trm_fvar X))) →
      PossibleTypes (Nat.succ n) (Trm.trm_abs V e1) (Typ.typ_all V' T1')
  | pt_all_shallow : ∀ {V V' e1 T1'},
      Wfe [] (Trm.trm_abs V e1) → Wft [] (Typ.typ_all V' T1') →
      PossibleTypes 0 (Trm.trm_abs V e1) (Typ.typ_all V' T1')
  | pt_sel : ∀ {n v S}, PossibleTypes n v S → PossibleTypes n v (Typ.typ_sel (Trm.trm_mem S))
  | pt_and : ∀ {n v T1 T2}, PossibleTypes n v T1 → PossibleTypes n v T2 → PossibleTypes n v (Typ.typ_and T1 T2)
  | pt_or1 : ∀ {n v T1 T2}, PossibleTypes n v T1 → Wft [] T2 → PossibleTypes n v (Typ.typ_or T1 T2)
  | pt_or2 : ∀ {n v T1 T2}, PossibleTypes n v T2 → Wft [] T1 → PossibleTypes n v (Typ.typ_or T1 T2)

end Lp2lc.Active.Ddia
