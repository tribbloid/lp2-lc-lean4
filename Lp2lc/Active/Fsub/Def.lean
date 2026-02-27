/-***************************************************************************
* Preservation and Progress for System-F with Subtyping - Definitions      *
* Brian Aydemir & Arthur Charguéraud, March 2007                           *
***************************************************************************-/
import Mathlib.Tactic

import Aesop
import «Lp2lc».Active.Shared
namespace Lp2lc.Active.Fsub

-- Var and Vars are provided by Shared

-- line 17
inductive Typ : Type where
  | typ_top   : Typ
  | typ_bvar  : Nat -> Typ
  | typ_fvar  : Var -> Typ
  | typ_arrow : Typ -> Typ -> Typ
  | typ_all   : Typ -> Typ -> Typ

-- line 26
inductive Trm : Type where
  | trm_bvar : Nat -> Trm
  | trm_fvar : Var -> Trm
  | trm_abs  : Typ -> Trm -> Trm
  | trm_app  : Trm -> Trm -> Trm
  | trm_tabs : Typ -> Trm -> Trm
  | trm_tapp : Trm -> Typ -> Trm

-- line 36
def open_tt_rec (K : Nat) (U : Typ) (T : Typ) : Typ :=
  match T with
  | Typ.typ_top         => Typ.typ_top
  | Typ.typ_bvar J      => if K = J then U else (Typ.typ_bvar J)
  | Typ.typ_fvar X      => Typ.typ_fvar X
  | Typ.typ_arrow T1 T2 => Typ.typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | Typ.typ_all T1 T2   => Typ.typ_all (open_tt_rec K U T1) (open_tt_rec (K + 1) U T2)

-- line 45
def open_tt (T : Typ) (U : Typ) : Typ := open_tt_rec 0 U T

-- line 49
def open_te_rec (K : Nat) (U : Typ) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i    => Trm.trm_bvar i
  | Trm.trm_fvar x    => Trm.trm_fvar x
  | Trm.trm_abs V e1  => Trm.trm_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | Trm.trm_app e1 e2 => Trm.trm_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | Trm.trm_tabs V e1 => Trm.trm_tabs (open_tt_rec K U V)  (open_te_rec (K + 1) U e1)
  | Trm.trm_tapp e1 V => Trm.trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)

-- line 59
def open_te (t : Trm) (U : Typ) : Trm := open_te_rec 0 U t

-- line 63
def open_ee_rec (k : Nat) (f : Trm) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i    => if k = i then f else (Trm.trm_bvar i)
  | Trm.trm_fvar x    => Trm.trm_fvar x
  | Trm.trm_abs V e1  => Trm.trm_abs V (open_ee_rec (k + 1) f e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | Trm.trm_tabs V e1 => Trm.trm_tabs V (open_ee_rec k f e1)
  | Trm.trm_tapp e1 V => Trm.trm_tapp (open_ee_rec k f e1) V

-- line 73
def open_ee (t : Trm) (u : Trm) : Trm := open_ee_rec 0 u t

-- line 77
notation:67 T " open_tt_var " X => open_tt T (Typ.typ_fvar X)
-- line 78
notation:67 t " open_te_var " X => open_te t (Typ.typ_fvar X)
-- line 79
notation:67 t " open_ee_var " x => open_ee t (Trm.trm_fvar x)

-- line 83
inductive DefType : Typ -> Prop where
  | type_top :
      DefType Typ.typ_top
  | type_var : (X : Var) ->
      DefType (Typ.typ_fvar X)
  | type_arrow : (T1 T2 : Typ) ->
      DefType T1 ->
      DefType T2 ->
      DefType (Typ.typ_arrow T1 T2)
  | type_all : (L : Vars) -> (T1 T2 : Typ) ->
      DefType T1 ->
      (∀ (X : Var), X ∉ L -> DefType (T2 open_tt_var X)) ->
      DefType (Typ.typ_all T1 T2)

-- line 99
inductive DefTerm : Trm -> Prop where
  | term_var : (x : Var) ->
      DefTerm (Trm.trm_fvar x)
  | term_abs : (L : Vars) -> (V : Typ) -> (e1 : Trm) ->
      DefType V ->
      (∀ (x : Var), x ∉ L -> DefTerm (e1 open_ee_var x)) ->
      DefTerm (Trm.trm_abs V e1)
  | term_app : (e1 e2 : Trm) ->
      DefTerm e1 ->
      DefTerm e2 ->
      DefTerm (Trm.trm_app e1 e2)
  | term_tabs : (L : Vars) -> (V : Typ) -> (e1 : Trm) ->
      DefType V ->
      (∀ (X : Var), X ∉ L -> DefTerm (e1 open_te_var X)) ->
      DefTerm (Trm.trm_tabs V e1)
  | term_tapp : (e1 : Trm) -> (V : Typ) ->
      DefTerm e1 ->
      DefType V ->
      DefTerm (Trm.trm_tapp e1 V)

-- line 123
inductive Bind : Type where
  | bind_sub : Typ -> Bind -- subtyping asumption
  | bind_typ : Typ -> Bind --typing assumption

-- line 133
notation "Env" => List (Var × Bind)

-- line 140
inductive Wft : Env -> Typ -> Prop where
  | wft_top : (E : Env) ->
      Wft E Typ.typ_top
  | wft_var : (U : Typ) -> (E : Env) -> (X : Var) ->
      Env.bindsOf X (Bind.bind_sub U) E ->
      Wft E (Typ.typ_fvar X)
  | wft_arrow : (E : Env) -> (T1 T2 : Typ) ->
      Wft E T1 ->
      Wft E T2 ->
      Wft E (Typ.typ_arrow T1 T2)
  | wft_all : (L : Vars) -> (E : Env) -> (T1 T2 : Typ) ->
      Wft E T1 ->
      (∀ (X : Var), X ∉ L ->
        Wft ((X, Bind.bind_sub T1) :: E) (T2 open_tt_var X)) ->
      Wft E (Typ.typ_all T1 T2)

-- line 161
inductive Okt : Env -> Prop where
  | okt_empty :
      Okt []
  | okt_sub : (E : Env) -> (X : Var) -> (T : Typ) ->
      Okt E -> Wft E T -> E.lookup X = none -> Okt ((X, Bind.bind_sub T) :: E)
  | okt_typ : (E : Env) -> (x : Var) -> (T : Typ) ->
      Okt E -> Wft E T -> E.lookup x = none -> Okt ((x, Bind.bind_typ T) :: E)

-- line 169
inductive Sub : Env -> Typ -> Typ -> Prop where
  | sub_top : (E : Env) -> (S : Typ) ->
      Okt E ->
      Wft E S ->
      Sub E S Typ.typ_top
  | sub_refl_tvar : (E : Env) -> (X : Var) ->
      Okt E ->
      Wft E (Typ.typ_fvar X) ->
      Sub E (Typ.typ_fvar X) (Typ.typ_fvar X)
  | sub_trans_tvar : (U : Typ) -> (E : Env) -> (T : Typ) -> (X : Var) ->
      Env.bindsOf X (Bind.bind_sub U) E ->
      Sub E U T ->
      Sub E (Typ.typ_fvar X) T
  | sub_arrow : (E : Env) -> (S1 S2 T1 T2 : Typ) ->
      Sub E T1 S1 ->
      Sub E S2 T2 ->
      Sub E (Typ.typ_arrow S1 S2) (Typ.typ_arrow T1 T2)
  | sub_all : (L : Vars) -> (E : Env) -> (S1 S2 T1 T2 : Typ) ->
      Sub E T1 S1 ->
      (∀ (X : Var), X ∉ L ->
          Sub ((X, Bind.bind_sub T1) :: E) (S2 open_tt_var X) (T2 open_tt_var X)) ->
      Sub E (Typ.typ_all S1 S2) (Typ.typ_all T1 T2)

-- line 195
inductive Typing : Env -> Trm -> Typ -> Prop where
  | typing_var : (E : Env) -> (x : Var) -> (T : Typ) ->
      Okt E ->
      Env.bindsOf x (Bind.bind_typ T) E ->
      Typing E (Trm.trm_fvar x) T
  | typing_abs : (L : Vars) -> (E : Env) -> (V : Typ) -> (e1 : Trm) -> (T1 : Typ) ->
      (∀ (x : Var), x ∉ L ->
        Typing ((x, Bind.bind_typ V) :: E) (e1 open_ee_var x) T1) ->
      Typing E (Trm.trm_abs V e1) (Typ.typ_arrow V T1)
  | typing_app : (T1 : Typ) -> (E : Env) -> (e1 e2 : Trm) -> (T2 : Typ) ->
      Typing E e1 (Typ.typ_arrow T1 T2) ->
      Typing E e2 T1 ->
      Typing E (Trm.trm_app e1 e2) T2
  | typing_tabs : (L : Vars) -> (E : Env) -> (V : Typ) -> (e1 : Trm) -> (T1 : Typ) ->
      (∀ (X : Var), X ∉ L ->
        Typing ((X, Bind.bind_sub V) :: E) (e1 open_te_var X) (T1 open_tt_var X)) ->
      Typing E (Trm.trm_tabs V e1) (Typ.typ_all V T1)
  | typing_tapp : (T1 : Typ) -> (E : Env) -> (e1 : Trm) -> (T T2 : Typ) ->
      Typing E e1 (Typ.typ_all T1 T2) ->
      Sub E T T1 ->
      Typing E (Trm.trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : (S : Typ) -> (E : Env) -> (e : Trm) -> (T : Typ) ->
      Typing E e S ->
      Sub E S T ->
      Typing E e T

-- line 223
inductive Value : Trm -> Prop where
  | value_abs  : (V : Typ) -> (e1 : Trm) -> DefTerm (Trm.trm_abs V e1) ->
                 Value (Trm.trm_abs V e1)
  | value_tabs : (V : Typ) -> (e1 : Trm) -> DefTerm (Trm.trm_tabs V e1) ->
                 Value (Trm.trm_tabs V e1)

-- line 231
inductive Red : Trm -> Trm -> Prop where
  | red_app_1 : (e1 e1' e2 : Trm) ->
      DefTerm e2 ->
      Red e1 e1' ->
      Red (Trm.trm_app e1 e2) (Trm.trm_app e1' e2)
  | red_app_2 : (e1 e2 e2' : Trm) ->
      Value e1 ->
      Red e2 e2' ->
      Red (Trm.trm_app e1 e2) (Trm.trm_app e1 e2')
  | red_tapp : (e1 e1' : Trm) -> (V : Typ) ->
      DefType V ->
      Red e1 e1' ->
      Red (Trm.trm_tapp e1 V) (Trm.trm_tapp e1' V)
  | red_abs : (V : Typ) -> (e1 : Trm) -> (v2 : Trm) ->
      DefTerm (Trm.trm_abs V e1) ->
      Value v2 ->
      Red (Trm.trm_app (Trm.trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : (V1 : Typ) -> (e1 : Trm) -> (V2 : Typ) ->
      DefTerm (Trm.trm_tabs V1 e1) ->
      DefType V2 ->
      Red (Trm.trm_tapp (Trm.trm_tabs V1 e1) V2) (open_te e1 V2)

-- line 256
def preservation : Prop := ∀ (E : Env) (e e' : Trm) (T : Typ),
  Typing E e T ->
  Red e e' ->
  Typing E e' T

-- line 260
def progress : Prop := ∀ (e : Trm) (T : Typ),
  Typing [] e T ->
  Value e ∨ (∃ e', Red e e')

-- line 275
def fv_tt (T : Typ) : Vars :=
  match T with
  | Typ.typ_top         => ∅
  | Typ.typ_bvar _      => ∅
  | Typ.typ_fvar X      => {X}
  | Typ.typ_arrow T1 T2 => (fv_tt T1) ∪ (fv_tt T2)
  | Typ.typ_all T1 T2   => (fv_tt T1) ∪ (fv_tt T2)

-- line 286
def fv_te (e : Trm) : Vars :=
  match e with
  | Trm.trm_bvar _    => ∅
  | Trm.trm_fvar _    => ∅
  | Trm.trm_abs V e1  => (fv_tt V) ∪ (fv_te e1)
  | Trm.trm_app e1 e2 => (fv_te e1) ∪ (fv_te e2)
  | Trm.trm_tabs V e1 => (fv_tt V) ∪ (fv_te e1)
  | Trm.trm_tapp e1 V => (fv_tt V) ∪ (fv_te e1)

-- line 298
def fv_ee (e : Trm) : Vars :=
  match e with
  | Trm.trm_bvar _    => ∅
  | Trm.trm_fvar x    => {x}
  | Trm.trm_abs _ e1  => (fv_ee e1)
  | Trm.trm_app e1 e2 => (fv_ee e1) ∪ (fv_ee e2)
  | Trm.trm_tabs _ e1 => (fv_ee e1)
  | Trm.trm_tapp e1 _ => (fv_ee e1)

-- line 310
def subst_tt (Z : Var) (U : Typ) (T : Typ) : Typ :=
  match T with
  | Typ.typ_top         => Typ.typ_top
  | Typ.typ_bvar J      => Typ.typ_bvar J
  | Typ.typ_fvar X      => by
      classical
      exact (if h : X = Z then (by simpa [h] using U) else Typ.typ_fvar X)
  | Typ.typ_arrow T1 T2 => Typ.typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | Typ.typ_all T1 T2   => Typ.typ_all (subst_tt Z U T1) (subst_tt Z U T2)

-- line 321
def subst_te (Z : Var) (U : Typ) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i    => Trm.trm_bvar i
  | Trm.trm_fvar x    => Trm.trm_fvar x
  | Trm.trm_abs V e1  => Trm.trm_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | Trm.trm_app e1 e2 => Trm.trm_app  (subst_te Z U e1) (subst_te Z U e2)
  | Trm.trm_tabs V e1 => Trm.trm_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | Trm.trm_tapp e1 V => Trm.trm_tapp (subst_te Z U e1) (subst_tt Z U V)

-- line 333
def subst_ee (z : Var) (u : Trm) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i    => Trm.trm_bvar i
  | Trm.trm_fvar x    => by
      classical
      exact (if h : x = z then (by simpa [h] using u) else Trm.trm_fvar x)
  | Trm.trm_abs V e1  => Trm.trm_abs V (subst_ee z u e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (subst_ee z u e1) (subst_ee z u e2)
  | Trm.trm_tabs V e1 => Trm.trm_tabs V (subst_ee z u e1)
  | Trm.trm_tapp e1 V => Trm.trm_tapp (subst_ee z u e1) V

-- line 345
def subst_tb (Z : Var) (P : Typ) (b : Bind) : Bind :=
  match b with
  | Bind.bind_sub T => Bind.bind_sub (subst_tt Z P T)
  | Bind.bind_typ T => Bind.bind_typ (subst_tt Z P T)

-- Map a type substitution over an environment
def map_subst_tb (Z : Var) (P : Typ) (E : Env) : Env :=
  Env.mapSecond (subst_tb Z P) E

end Lp2lc.Active.Fsub
