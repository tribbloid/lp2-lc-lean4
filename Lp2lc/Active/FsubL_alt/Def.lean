import Std
import Mathlib.Data.Finset.Basic
import Aesop
import «Lp2lc».Shared

namespace Lp2lc.Active.FsubL_alt

/-- [Coq L30] -/ 
inductive typ : Type where
  | typ_top   : typ
  | typ_bot   : typ
  | typ_bvar  : Nat -> typ
  | typ_fvar  : Var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all   : typ -> typ -> typ -> typ
  deriving BEq, DecidableEq

/-- [Coq L40] -/
inductive trm : Type where
  | trm_bvar : Nat -> trm
  | trm_fvar : Var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_tabs : typ -> typ -> trm -> trm
  | trm_tapp : trm -> typ -> trm
  deriving BEq, DecidableEq

open typ trm

/-- [Coq L50] -/ 
def open_tt_rec (K : Nat) (U : typ) (T : typ) : typ :=
  match T with
  | typ_top         => typ_top
  | typ_bot         => typ_bot
  | typ_bvar J      => if K = J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T0 T1 T2 => typ_all (open_tt_rec K U T0) (open_tt_rec K U T1) (open_tt_rec (K + 1) U T2)

/-- [Coq L60] -/ 
def open_tt (T : typ) (U : typ) : typ := open_tt_rec 0 U T

/-- [Coq L64] -/
def open_te_rec (K : Nat) (U : typ) (e : trm) : trm :=
  match e with
  | trm_bvar i          => trm_bvar i
  | trm_fvar x          => trm_fvar x
  | trm_abs V e1        => trm_abs (open_tt_rec K U V) (open_te_rec K U e1)
  | trm_app e1 e2       => trm_app (open_te_rec K U e1) (open_te_rec K U e2)
  | trm_tabs VS VU e1   => trm_tabs (open_tt_rec K U VS) (open_tt_rec K U VU) (open_te_rec (K + 1) U e1)
  | trm_tapp e1 V       => trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)

/-- [Coq L74] -/ 
def open_te (t : trm) (U : typ) : trm := open_te_rec 0 U t

/-- [Coq L78] -/
def open_ee_rec (k : Nat) (f : trm) (e : trm) : trm :=
  match e with
  | trm_bvar i          => if k = i then f else (trm_bvar i)
  | trm_fvar x          => trm_fvar x
  | trm_abs V e1        => trm_abs V (open_ee_rec (k + 1) f e1)
  | trm_app e1 e2       => trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | trm_tabs VS VU e1   => trm_tabs VS VU (open_ee_rec k f e1)
  | trm_tapp e1 V       => trm_tapp (open_ee_rec k f e1) V

/-- [Coq L88] -/ 
def open_ee (t : trm) (u : trm) : trm := open_ee_rec 0 u t

/-- [Coq L92-95] -/ 
notation:67 T " open_tt_var " X => open_tt T (typ.typ_fvar X)
notation:67 t " open_te_var " X => open_te t (typ.typ_fvar X)
notation:67 t " open_ee_var " x => open_ee t (trm.trm_fvar x)

/-- [Coq L98-114] -/
inductive def_type : typ -> Prop where
  | type_top : def_type typ_top
  | type_bot : def_type typ_bot
  | type_var : (X : Var) -> def_type (typ_fvar X)
  | type_arrow : (T1 T2 : typ) -> def_type T1 -> def_type T2 -> def_type (typ_arrow T1 T2)
  | type_all : (L : Vars) -> (T0 T1 T2 : typ) ->
      def_type T0 ->
      def_type T1 ->
      (∀ (X : Var), X ∉ L -> def_type (T2 open_tt_var X)) ->
      def_type (typ_all T0 T1 T2)

/-- [Coq L117-136] -/
inductive def_term : trm -> Prop where
  | term_var : (x : Var) -> def_term (trm_fvar x)
  | term_abs : (L : Vars) -> (V : typ) -> (e1 : trm) ->
      def_type V ->
      (∀ (x : Var), x ∉ L -> def_term (e1 open_ee_var x)) ->
      def_term (trm_abs V e1)
  | term_app : (e1 e2 : trm) -> def_term e1 -> def_term e2 -> def_term (trm_app e1 e2)
  | term_tabs : (L : Vars) -> (VS VU : typ) -> (e1 : trm) ->
      def_type VS -> def_type VU ->
      (∀ (X : Var), X ∉ L -> def_term (e1 open_te_var X)) ->
      def_term (trm_tabs VS VU e1)
  | term_tapp : (e1 : trm) -> (V : typ) -> def_term e1 -> def_type V -> def_term (trm_tapp e1 V)

/-- [Coq L140-146] -/
inductive bind : Type where
  | bind_sub : typ -> typ -> bind
  | bind_typ : typ -> bind
  deriving BEq, DecidableEq

/-- [Coq L146] -/
abbrev env := List (Var × bind)

/-- [Coq L146-171] -/ 
namespace Env
  def dom (E : env) : Vars := Lp2lc.Active.Env.domOf E
end Env

/-- [Coq L146-171] -/ 
/-- LibEnv-like binds: lookup exact binding. -/
@[simp] def binds (x : Var) (b : bind) (E : env) : Prop := E.lookup x = some b

/-- [Coq L153-171] -/
inductive wft : env -> typ -> Prop where
  | wft_top : (E : env) -> wft E typ_top
  | wft_bot : (E : env) -> wft E typ_bot
  | wft_var : (T0 T1 : typ) -> (E : env) -> (X : Var) ->
      binds X (bind.bind_sub T0 T1) E ->
      wft E (typ_fvar X)
  | wft_arrow : (E : env) -> (T1 T2 : typ) -> wft E T1 -> wft E T2 -> wft E (typ_arrow T1 T2)
  | wft_all : (L : Vars) -> (E : env) -> (T0 T1 T2 : typ) ->
      wft E T0 -> wft E T1 ->
      (∀ (X : Var), X ∉ L -> wft ((X, bind.bind_sub T0 T1) :: E) (T2 open_tt_var X)) ->
      wft E (typ_all T0 T1 T2)

/-- [Coq L176-183] -/
inductive okt : env -> Prop where
  | okt_empty : okt []
  | okt_sub : (E : env) -> (X : Var) -> (T0 T1 : typ) ->
      okt E -> wft E T0 -> wft E T1 -> E.lookup X = none -> okt ((X, bind.bind_sub T0 T1) :: E)
  | okt_typ : (E : env) -> (x : Var) -> (T : typ) ->
      okt E -> wft E T -> E.lookup x = none -> okt ((x, bind.bind_typ T) :: E)

/-- [Coq L186-221] -/
inductive sub : env -> typ -> typ -> Prop where
  | sub_top : (E : env) -> (S : typ) -> okt E -> wft E S -> sub E S typ_top
  | sub_bot : (E : env) -> (T : typ) -> okt E -> wft E T -> sub E typ_bot T
  | sub_refl_tvar : (E : env) -> (X : Var) -> okt E -> wft E (typ_fvar X) -> sub E (typ_fvar X) (typ_fvar X)
  | sub_tvar : (T0 T1 : typ) -> (E : env) -> (X : Var) ->
      okt E -> binds X (bind.bind_sub T0 T1) E -> sub E (typ_fvar X) T1
  | sub_tvar_lower : (T0 T1 : typ) -> (E : env) -> (X : Var) ->
      okt E -> binds X (bind.bind_sub T0 T1) E -> sub E T0 (typ_fvar X)
  | sub_arrow : (E : env) -> (S1 S2 T1 T2 : typ) ->
      sub E T1 S1 -> sub E S2 T2 -> sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : (L : Vars) -> (E : env) -> (S0 S1 S2 T0 T1 T2 : typ) ->
      sub E S0 T0 -> sub E T1 S1 ->
      (∀ (X : Var), X ∉ L -> sub ((X, bind.bind_sub T0 T1) :: E) (S2 open_tt_var X) (T2 open_tt_var X)) ->
      sub E (typ_all S0 S1 S2) (typ_all T0 T1 T2)
  | sub_trans : (E : env) -> (S T U : typ) -> sub E S T -> sub E T U -> sub E S U

/-- [Coq L224-251] -/
inductive typing : env -> trm -> typ -> Prop where
  | typing_var : (E : env) -> (x : Var) -> (T : typ) ->
      okt E -> binds x (bind.bind_typ T) E -> typing E (trm_fvar x) T
  | typing_abs : (L : Vars) -> (E : env) -> (V : typ) -> (e1 : trm) -> (T1 : typ) ->
      (∀ (x : Var), x ∉ L -> typing ((x, bind.bind_typ V) :: E) (e1 open_ee_var x) T1) ->
      typing E (trm_abs V e1) (typ_arrow V T1)
  | typing_app : (T1 : typ) -> (E : env) -> (e1 e2 : trm) -> (T2 : typ) ->
      typing E e1 (typ_arrow T1 T2) -> typing E e2 T1 -> typing E (trm_app e1 e2) T2
  | typing_tabs : (L : Vars) -> (E : env) -> (VS VU : typ) -> (e1 : trm) -> (T1 : typ) ->
      (∀ (X : Var), X ∉ L -> typing ((X, bind.bind_sub VS VU) :: E) (e1 open_te_var X) (T1 open_tt_var X)) ->
      typing E (trm_tabs VS VU e1) (typ_all VS VU T1)
  | typing_tapp : (T0 T1 : typ) -> (E : env) -> (e1 : trm) -> (T T2 : typ) ->
      typing E e1 (typ_all T0 T1 T2) -> sub E T0 T -> sub E T T1 -> typing E (trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : (S : typ) -> (E : env) -> (e : trm) -> (T : typ) -> typing E e S -> sub E S T -> typing E e T

/-- [Coq L254-259] -/
inductive value : trm -> Prop where
  | value_abs  : (V : typ) -> (e1 : trm) -> def_term (trm_abs V e1) -> value (trm_abs V e1)
  | value_tabs : (VS VU : typ) -> (e1 : trm) -> def_term (trm_tabs VS VU e1) -> value (trm_tabs VS VU e1)

/-- [Coq L262-283] -/
inductive red : trm -> trm -> Prop where
  | red_app_1 : (e1 e1' e2 : trm) -> def_term e2 -> red e1 e1' -> red (trm_app e1 e2) (trm_app e1' e2)
  | red_app_2 : (e1 e2 e2' : trm) -> value e1 -> red e2 e2' -> red (trm_app e1 e2) (trm_app e1 e2')
  | red_tapp : (e1 e1' : trm) -> (V : typ) -> def_type V -> red e1 e1' -> red (trm_tapp e1 V) (trm_tapp e1' V)
  | red_abs : (V : typ) -> (e1 : trm) -> (v2 : trm) -> def_term (trm_abs V e1) -> value v2 -> red (trm_app (trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : (V0 V1 : typ) -> (e1 : trm) -> (V2 : typ) -> def_term (trm_tabs V0 V1 e1) -> def_type V2 -> red (trm_tapp (trm_tabs V0 V1 e1) V2) (open_te e1 V2)

/-- [Coq L286-295] -/
@[simp] def preservation : Prop := ∀ (e e' : trm) (T : typ), typing [] e T -> red e e' -> typing [] e' T

/-- [Coq L291-295] -/
@[simp] def progress : Prop := ∀ (e : trm) (T : typ), typing [] e T -> value e ∨ (∃ e', red e e')

/-- [Coq L303-313] -/
@[simp] def fv_tt (T : typ) : Vars :=
  match T with
  | typ_top           => ∅
  | typ_bot           => ∅
  | typ_bvar _        => ∅
  | typ_fvar X        => {X}
  | typ_arrow T1 T2   => (fv_tt T1) ∪ (fv_tt T2)
  | typ_all T0 T1 T2  => (fv_tt T0) ∪ (fv_tt T1) ∪ (fv_tt T2)

/-- [Coq L317-325] -/
@[simp] def fv_te (e : trm) : Vars :=
  match e with
  | trm_bvar _        => ∅
  | trm_fvar _        => ∅
  | trm_abs V e1      => (fv_tt V) ∪ (fv_te e1)
  | trm_app e1 e2     => (fv_te e1) ∪ (fv_te e2)
  | trm_tabs VS VU e1 => (fv_tt VS) ∪ (fv_tt VU) ∪ (fv_te e1)
  | trm_tapp e1 V     => (fv_tt V) ∪ (fv_te e1)

/-- [Coq L329-337] -/
@[simp] def fv_ee (e : trm) : Vars :=
  match e with
  | trm_bvar _        => ∅
  | trm_fvar x        => {x}
  | trm_abs _ e1      => (fv_ee e1)
  | trm_app e1 e2     => (fv_ee e1) ∪ (fv_ee e2)
  | trm_tabs _ _ e1   => (fv_ee e1)
  | trm_tapp e1 _     => (fv_ee e1)

/-- [Coq L341-349] -/
@[simp] def subst_tt (Z : Var) (U : typ) (T : typ) : typ :=
  match T with
  | typ_top           => typ_top
  | typ_bot           => typ_bot
  | typ_bvar J        => typ_bvar J
  | typ_fvar X        => by
      classical
      exact (if h : X = Z then (by simpa [h] using U) else typ_fvar X)
  | typ_arrow T1 T2   => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T0 T1 T2  => typ_all (subst_tt Z U T0) (subst_tt Z U T1) (subst_tt Z U T2)

/-- [Coq L353-361] -/
@[simp] def subst_te (Z : Var) (U : typ) (e : trm) : trm :=
  match e with
  | trm_bvar i        => trm_bvar i
  | trm_fvar x        => trm_fvar x
  | trm_abs V e1      => trm_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | trm_app e1 e2     => trm_app  (subst_te Z U e1) (subst_te Z U e2)
  | trm_tabs VS VU e1 => trm_tabs (subst_tt Z U VS) (subst_tt Z U VU) (subst_te Z U e1)
  | trm_tapp e1 V     => trm_tapp (subst_te Z U e1) (subst_tt Z U V)

/-- [Coq L365-373] -/
@[simp] def subst_ee (z : Var) (u : trm) (e : trm) : trm :=
  match e with
  | trm_bvar i        => trm_bvar i
  | trm_fvar x        => by
      classical
      exact (if h : x = z then (by simpa [h] using u) else trm_fvar x)
  | trm_abs V e1      => trm_abs V (subst_ee z u e1)
  | trm_app e1 e2     => trm_app (subst_ee z u e1) (subst_ee z u e2)
  | trm_tabs VS VU e1 => trm_tabs VS VU (subst_ee z u e1)
  | trm_tapp e1 V     => trm_tapp (subst_ee z u e1) V

/-- [Coq L376-382] -/
@[simp] def subst_tb (Z : Var) (P : typ) (b : bind) : bind :=
  match b with
  | bind.bind_sub T0 T1 => bind.bind_sub (subst_tt Z P T0) (subst_tt Z P T1)
  | bind.bind_typ T     => bind.bind_typ (subst_tt Z P T)

/-- Map substitution over environment -/
@[simp] def map_subst_tb (Z : Var) (P : typ) (E : env) : env :=
  E.map (fun p => (p.1, subst_tb Z P p.2))

end Lp2lc.Active.FsubL_alt
