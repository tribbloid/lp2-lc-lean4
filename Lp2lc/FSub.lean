
import Std

namespace Lp2lc.FSub

structure Var where
  name: String
deriving BEq, Hashable, Inhabited, DecidableEq

/- We use section variables to represent both term and type variables -/

-- variable (x : Var) -- For term variables
-- variable (X : Var) -- For type variables

/- Description of the Language -/

/- Representation of pre-types -/
inductive Typ : Type where
  | typ_top   : Typ
  | typ_bvar  : Nat → Typ
  | typ_fvar  : Var → Typ
  | typ_arrow : Typ → Typ → Typ
  | typ_all   : Typ → Typ → Typ
  deriving BEq, Inhabited

/- Representation of pre-terms -/
inductive Trm : Type where
  | trm_bvar : Nat → Trm
  | trm_fvar : Var → Trm
  | trm_abs  : Typ → Trm → Trm
  | trm_app  : Trm → Trm → Trm
  | trm_tabs : Typ → Trm → Trm
  | trm_tapp : Trm → Typ → Trm
  deriving BEq, Inhabited

/- Opening up a type binder occurring in a type -/
def open_tt_rec (k : Nat) (u : Typ) : Typ → Typ
  | Typ.typ_top => Typ.typ_top
  | Typ.typ_bvar j => if k = j then u else Typ.typ_bvar j
  | Typ.typ_fvar x => Typ.typ_fvar x
  | Typ.typ_arrow t1 t2 => Typ.typ_arrow (open_tt_rec k u t1) (open_tt_rec k u t2)
  | Typ.typ_all t1 t2 => Typ.typ_all (open_tt_rec k u t1) (open_tt_rec (k + 1) u t2)

def open_tt (t u : Typ) : Typ := open_tt_rec 0 u t

/- Opening up a type binder occurring in a term -/
def open_te_rec (k : Nat) (u : Typ) : Trm → Trm
  | Trm.trm_bvar i => Trm.trm_bvar i
  | Trm.trm_fvar x => Trm.trm_fvar x
  | Trm.trm_abs v e1 => Trm.trm_abs (open_tt_rec k u v) (open_te_rec k u e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (open_te_rec k u e1) (open_te_rec k u e2)
  | Trm.trm_tabs v e1 => Trm.trm_tabs (open_tt_rec k u v) (open_te_rec (k + 1) u e1)
  | Trm.trm_tapp e1 v => Trm.trm_tapp (open_te_rec k u e1) (open_tt_rec k u v)

def open_te (t : Trm) (u : Typ) : Trm := open_te_rec 0 u t

/- Opening up a term binder occurring in a term -/
def open_ee_rec (k : Nat) (f : Trm) : Trm → Trm
  | Trm.trm_bvar i => if k = i then f else Trm.trm_bvar i
  | Trm.trm_fvar x => Trm.trm_fvar x
  | Trm.trm_abs v e1 => Trm.trm_abs v (open_ee_rec (k + 1) f e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | Trm.trm_tabs v e1 => Trm.trm_tabs v (open_ee_rec k f e1)
  | Trm.trm_tapp e1 v => Trm.trm_tapp (open_ee_rec k f e1) v

def open_ee (t u : Trm) : Trm := open_ee_rec 0 u t

/- Notation for opening up binders with type or term variables -/
def open_tt_var (t : Typ) (x : Var) : Typ := open_tt t (Typ.typ_fvar x)
def open_te_var (t : Trm) (x : Var) : Trm := open_te t (Typ.typ_fvar x)
def open_ee_var (t : Trm) (x : Var) : Trm := open_ee t (Trm.trm_fvar x)

/- Types as locally closed pre-types -/

inductive type : Typ → Prop where
  | type_top :
      type Typ.typ_top
  | type_var : (X : Var) →
      type (Typ.typ_fvar X)
  | type_arrow : (T1 T2 : Typ) →
      type T1 →
      type T2 →
      type (Typ.typ_arrow T1 T2)
  | type_all : (L : Std.HashSet Var) → (T1 T2 : Typ) →
      type T1 →
      (∀ X, X ∉ L → type (open_tt_var T2 X)) →
      type (Typ.typ_all T1 T2)

/- Terms as locally closed pre-terms -/

inductive term : Trm → Prop where
  | term_var : (x : Var) →
      term (Trm.trm_fvar x)
  | term_abs : (L : Std.HashSet Var) → (V : Typ) → (e1 : Trm) →
      type V →
      (∀ x, x ∉ L → term (open_ee_var e1 x)) →
      term (Trm.trm_abs V e1)
  | term_app : (e1 e2 : Trm) →
      term e1 →
      term e2 →
      term (Trm.trm_app e1 e2)
  | term_tabs : (L : Std.HashSet Var) → (V : Typ) → (e1 : Trm) →
      type V →
      (∀ X, X ∉ L → term (open_te_var e1 X)) →
      term (Trm.trm_tabs V e1)
  | term_tapp : (e1 : Trm) → (V : Typ) →
      term e1 →
      type V →
      term (Trm.trm_tapp e1 V)

/- Binding are either mapping type or term variables -/
inductive bind : Type where
  | bind_sub : Typ → bind
  | bind_typ : Typ → bind
  deriving BEq, Inhabited

/- Environment is an associative list of bindings -/
def env := Std.HashMap Var bind

/- Helper functions for environment bindings -/
def bindSubtype (E : env) (X : Var) (T : Typ) : env :=
  E.insert X (bind.bind_sub T)

def bindType (E : env) (x : Var) (T : Typ) : env :=
  E.insert x (bind.bind_typ T)

/- Notations for environment bindings -/
notation:23 E "," X " ~<: " T => bindSubtype E X T  -- type variable subtyping binding
notation:23 E "," x " ~: " T => bindType E x T      -- term variable typing binding

/- Well-formedness of a pre-type T in an environment E -/

inductive wft : env → Typ → Prop where
  | wft_top : (E : env) →
      wft E Typ.typ_top
  | wft_var : (U : Typ) → (E : env) → (X : Var) →
      E.contains X ∧ E.get! X = bind.bind_sub U →
      wft E (Typ.typ_fvar X)
  | wft_arrow : (E : env) → (T1 T2 : Typ) →
      wft E T1 →
      wft E T2 →
      wft E (Typ.typ_arrow T1 T2)
  | wft_all : (L : Std.HashSet Var) → (E : env) → (T1 T2 : Typ) →
      wft E T1 →
      (∀ X, X ∉ L →
        wft (E.insert X (bind.bind_sub T1)) (open_tt_var T2 X)) →
      wft E (Typ.typ_all T1 T2)

/- A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment -/

inductive okt : env → Prop where
  | okt_empty :
      okt (Std.HashMap.empty)
  | okt_sub : (E : env) → (X : Var) → (T : Typ) →
      okt E → wft E T → ¬E.contains X → okt (E.insert X (bind.bind_sub T))
  | okt_typ : (E : env) → (x : Var) → (T : Typ) →
      okt E → wft E T → ¬E.contains x → okt (E.insert x (bind.bind_typ T))

/- Subtyping relation -/
inductive sub : env → Typ → Typ → Prop where
  | sub_top : (E : env) → (S : Typ) →
      okt E →
      wft E S →
      sub E S Typ.typ_top
  | sub_refl_tvar : (E : env) → (X : Var) →
      okt E →
      wft E (Typ.typ_fvar X) →
      sub E (Typ.typ_fvar X) (Typ.typ_fvar X)
  | sub_trans_tvar : (U : Typ) → (E : env) → (T : Typ) → (X : Var) →
      (E.contains X ∧ E.get! X = bind.bind_sub U) →
      sub E U T →
      sub E (Typ.typ_fvar X) T
  | sub_arrow : (E : env) → (S1 S2 T1 T2 : Typ) →
      sub E T1 S1 →
      sub E S2 T2 →
      sub E (Typ.typ_arrow S1 S2) (Typ.typ_arrow T1 T2)
  | sub_all : (L : Std.HashSet Var) → (E : env) → (S1 S2 T1 T2 : Typ) →
      sub E T1 S1 →
      (∀ X, X ∉ L →
          sub (E.insert X (bind.bind_sub T1)) (open_tt_var S2 X) (open_tt_var T2 X)) →
      sub E (Typ.typ_all S1 S2) (Typ.typ_all T1 T2)

/- Typing relation -/
inductive typing : env → Trm → Typ → Prop where
  | typing_var : (E : env) → (x : Var) → (T : Typ) →
      okt E →
      (E.contains x ∧ E.get! x = bind.bind_typ T) →
      typing E (Trm.trm_fvar x) T
  | typing_abs : (L : Std.HashSet Var) → (E : env) → (V : Typ) → (e1 : Trm) → (T1 : Typ) →
      (∀ x, x ∉ L →
        typing (E.insert x (bind.bind_typ V)) (open_ee_var e1 x) T1) →
      typing E (Trm.trm_abs V e1) (Typ.typ_arrow V T1)
  | typing_app : (T1 : Typ) → (E : env) → (e1 e2 : Trm) → (T2 : Typ) →
      typing E e1 (Typ.typ_arrow T1 T2) →
      typing E e2 T1 →
      typing E (Trm.trm_app e1 e2) T2
  | typing_tabs : (L : Std.HashSet Var) → (E : env) → (V : Typ) → (e1 : Trm) → (T1 : Typ) →
      (∀ X, X ∉ L →
        typing (E.insert X (bind.bind_sub V)) (open_te_var e1 X) (open_tt_var T1 X)) →
      typing E (Trm.trm_tabs V e1) (Typ.typ_all V T1)
  | typing_tapp : (T1 : Typ) → (E : env) → (e1 : Trm) → (T T2 : Typ) →
      typing E e1 (Typ.typ_all T1 T2) →
      sub E T T1 →
      typing E (Trm.trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : (S : Typ) → (E : env) → (e : Trm) → (T : Typ) →
      typing E e S →
      sub E S T →
      typing E e T

/- Values -/
inductive value : Trm → Prop where
  | value_abs  : (V : Typ) → (e1 : Trm) → term (Trm.trm_abs V e1) →
      value (Trm.trm_abs V e1)
  | value_tabs : (V : Typ) → (e1 : Trm) → term (Trm.trm_tabs V e1) →
      value (Trm.trm_tabs V e1)

/- One-step reduction -/
inductive red : Trm → Trm → Prop where
  | red_app_1 : (e1 e1' e2 : Trm) →
      term e2 →
      red e1 e1' →
      red (Trm.trm_app e1 e2) (Trm.trm_app e1' e2)
  | red_app_2 : (e1 e2 e2' : Trm) →
      value e1 →
      red e2 e2' →
      red (Trm.trm_app e1 e2) (Trm.trm_app e1 e2')
  | red_tapp : (e1 e1' : Trm) → (V : Typ) →
      type V →
      red e1 e1' →
      red (Trm.trm_tapp e1 V) (Trm.trm_tapp e1' V)
  | red_abs : (V : Typ) → (e1 v2 : Trm) →
      term (Trm.trm_abs V e1) →
      value v2 →
      red (Trm.trm_app (Trm.trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : (V1 : Typ) → (e1 : Trm) → (V2 : Typ) →
      term (Trm.trm_tabs V1 e1) →
      type V2 →
      red (Trm.trm_tapp (Trm.trm_tabs V1 e1) V2) (open_te e1 V2)

/- Preservation and Progress properties -/
def preservation : Prop :=
  ∀ (E : env) (e e' : Trm) (T : Typ),
    typing E e T →
    red e e' →
    typing E e' T

def progress : Prop :=
  ∀ (e : Trm) (T : Typ),
    typing (Std.HashMap.empty) e T →
    value e ∨ (∃ e', red e e')

/- Computing free type variables in a type -/
def fv_tt : Typ → Std.HashSet Var
  | Typ.typ_top         => {}
  | Typ.typ_bvar _      => {}
  | Typ.typ_fvar X      => {X}
  | Typ.typ_arrow T1 T2 => fv_tt T1 ∪ fv_tt T2
  | Typ.typ_all T1 T2   => fv_tt T1 ∪ fv_tt T2

def fv_te : Trm → Std.HashSet Var
  | Trm.trm_bvar _    => {}
  | Trm.trm_fvar _    => {}
  | Trm.trm_abs V e1  => fv_tt V ∪ fv_te e1
  | Trm.trm_app e1 e2 => fv_te e1 ∪ fv_te e2
  | Trm.trm_tabs V e1 => fv_tt V ∪ fv_te e1
  | Trm.trm_tapp e1 V => fv_tt V ∪ fv_te e1

def fv_ee : Trm → Std.HashSet Var
  | Trm.trm_bvar _    => {}
  | Trm.trm_fvar x    => {x}
  | Trm.trm_abs _ e1  => fv_ee e1
  | Trm.trm_app e1 e2 => fv_ee e1 ∪ fv_ee e2
  | Trm.trm_tabs _ e1 => fv_ee e1
  | Trm.trm_tapp e1 _ => fv_ee e1

def subst_tt (Z : Var) (U : Typ) : Typ → Typ
  | Typ.typ_top         => Typ.typ_top
  | Typ.typ_bvar J      => Typ.typ_bvar J
  | Typ.typ_fvar X      => if X = Z then U else Typ.typ_fvar X
  | Typ.typ_arrow T1 T2 => Typ.typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | Typ.typ_all T1 T2   => Typ.typ_all (subst_tt Z U T1) (subst_tt Z U T2)

def subst_te (Z : Var) (U : Typ) : Trm → Trm
  | Trm.trm_bvar i      => Trm.trm_bvar i
  | Trm.trm_fvar x      => Trm.trm_fvar x
  | Trm.trm_abs V e1    => Trm.trm_abs (subst_tt Z U V) (subst_te Z U e1)
  | Trm.trm_app e1 e2   => Trm.trm_app (subst_te Z U e1) (subst_te Z U e2)
  | Trm.trm_tabs V e1   => Trm.trm_tabs (subst_tt Z U V) (subst_te Z U e1)
  | Trm.trm_tapp e1 V   => Trm.trm_tapp (subst_te Z U e1) (subst_tt Z U V)

def subst_ee (z : Var) (u : Trm) : Trm → Trm
  | Trm.trm_bvar i      => Trm.trm_bvar i
  | Trm.trm_fvar x      => if x = z then u else Trm.trm_fvar x
  | Trm.trm_abs V e1    => Trm.trm_abs V (subst_ee z u e1)
  | Trm.trm_app e1 e2   => Trm.trm_app (subst_ee z u e1) (subst_ee z u e2)
  | Trm.trm_tabs V e1   => Trm.trm_tabs V (subst_ee z u e1)
  | Trm.trm_tapp e1 V   => Trm.trm_tapp (subst_ee z u e1) V


-- All basic free variable and substitution infrastructure from the Coq source has been translated.

def subst_tb (Z : Var) (P : Typ) : bind → bind
  | bind.bind_sub T => bind.bind_sub (subst_tt Z P T)
  | bind.bind_typ T => bind.bind_typ (subst_tt Z P T)



end Lp2lc.FSub
