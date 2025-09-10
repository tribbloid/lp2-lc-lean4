import Std
import Mathlib.Data.Finset.Basic
import Aesop
import «Lp2lc».Shared

namespace Lp2lc.Active.Dsub

/-- [Coq L24] -/ 
inductive typ : Type where
  | typ_top   : typ
  | typ_sel   : trm -> typ
  | typ_mem   : Bool -> typ -> typ
  | typ_all   : typ -> typ -> typ
  deriving BEq, DecidableEq

/-- [Coq L32] -/ 
inductive trm : Type where
  | trm_bvar : Nat -> trm
  | trm_fvar : Var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_mem  : typ -> trm
  | trm_app  : trm -> trm -> trm
  deriving BEq, DecidableEq

open typ trm

/-- [Coq L39-56] Opening (mutual) -/ 
mutual
  def open_t_rec (k : Nat) (f : trm) (T : typ) : typ :=
    match T with
    | typ_top           => typ_top
    | typ_sel t         => typ_sel (open_e_rec k f t)
    | typ_mem b T1      => typ_mem b (open_t_rec k f T1)
    | typ_all T1 T2     => typ_all (open_t_rec k f T1) (open_t_rec (k + 1) f T2)

  def open_e_rec (k : Nat) (f : trm) (e : trm) : trm :=
    match e with
    | trm_bvar i        => if k = i then f else (trm_bvar i)
    | trm_fvar x        => trm_fvar x
    | trm_abs V e1      => trm_abs (open_t_rec k f V) (open_e_rec (k + 1) f e1)
    | trm_mem T         => trm_mem (open_t_rec k f T)
    | trm_app e1 e2     => trm_app (open_e_rec k f e1) (open_e_rec k f e2)
end

/-- [Coq L58-66] -/ 
@[simp] def open_t (T : typ) (f : trm) : typ := open_t_rec 0 f T
@[simp] def open_e (t : trm) (u : trm) : trm := open_e_rec 0 u t

/-- [Coq L63-65] -/
notation:67 T " open_t_var " x => open_t T (trm.trm_fvar x)
notation:67 t " open_e_var " x => open_e t (trm.trm_fvar x)

/-- [Coq L68-81] Local closure -/ 
inductive def_type : typ -> Prop where
  | type_top : def_type typ_top
  | type_sel : (e1 : trm) -> def_term e1 -> def_type (typ_sel e1)
  | type_mem : (b : Bool) -> (T1 : typ) -> def_type T1 -> def_type (typ_mem b T1)
  | type_all : (L : Vars) -> (T1 T2 : typ) ->
      def_type T1 ->
      (∀ (x : Var), x ∉ L -> def_type (T2 open_t_var x)) ->
      def_type (typ_all T1 T2)

/-- [Coq L83-97] -/ 
inductive def_term : trm -> Prop where
  | term_var : (x : Var) -> def_term (trm_fvar x)
  | term_abs : (L : Vars) -> (V : typ) -> (e1 : trm) ->
      def_type V -> (∀ (x : Var), x ∉ L -> def_term (e1 open_e_var x)) ->
      def_term (trm_abs V e1)
  | term_mem : (T1 : typ) -> def_type T1 -> def_term (trm_mem T1)
  | term_app : (e1 e2 : trm) -> def_term e1 -> def_term e2 -> def_term (trm_app e1 e2)

/-- [Coq L101-106] Values -/ 
inductive value : trm -> Prop where
  | value_abs  : (V : typ) -> (e1 : trm) -> def_term (trm_abs V e1) -> value (trm_abs V e1)
  | value_mem  : (V : typ) -> def_term (trm_mem V) -> value (trm_mem V)

/-- [Coq L109-111] -/ 
abbrev env := List (Var × typ)

namespace Env
  /-- domain of environment -/ 
  def dom (E : env) : Vars := Lp2lc.Active.Env.domOf E
end Env

/-- [Coq L126] -/ 
@[simp] def binds (x : Var) (T : typ) (E : env) : Prop := E.lookup x = some T

/-- [Coq L116-131] Wf type/env -/ 
mutual
  inductive wft : env -> typ -> Prop where
    | wft_top : (E : env) -> wft E typ_top
    | wft_sel : (E : env) -> (e : trm) ->
        (value e ∨ ∃ x, trm_fvar x = e) ->
        wfe E e ->
        wft E (typ_sel e)
    | wft_mem : (E : env) -> (b : Bool) -> (T1 : typ) ->
        wft E T1 ->
        wft E (typ_mem b T1)
    | wft_all : (L : Vars) -> (E : env) -> (T1 T2 : typ) ->
        wft E T1 ->
        (∀ (x : Var), x ∉ L -> wft ((x, T1) :: E) (T2 open_t_var x)) ->
        wft E (typ_all T1 T2)

  inductive wfe : env -> trm -> Prop where
    | wfe_var : (U : typ) -> (E : env) -> (x : Var) ->
        binds x U E ->
        wfe E (trm_fvar x)
    | wfe_abs : (L : Vars) -> (E : env) -> (V : typ) -> (e : trm) ->
        wft E V ->
        (∀ (x : Var), x ∉ L -> wfe ((x, V) :: E) (e open_e_var x)) ->
        wfe E (trm_abs V e)
    | wfe_mem : (E : env) -> (T : typ) ->
        wft E T ->
        wfe E (trm_mem T)
    | wfe_app : (E : env) -> (e1 e2 : trm) ->
        wfe E e1 -> wfe E e2 ->
        wfe E (trm_app e1 e2)
end

/-- [Coq L152-157] -/ 
inductive okt : env -> Prop where
  | okt_empty : okt []
  | okt_push : (E : env) -> (x : Var) -> (T : typ) ->
      okt E -> wft E T -> E.lookup x = none -> okt ((x, T) :: E)

/-- [Coq L160-205] Subtyping & has -/ 
mutual
  inductive sub : env -> typ -> typ -> Prop where
    | sub_top : (E : env) -> (S : typ) -> okt E -> wft E S -> sub E S typ_top
    | sub_refl_sel : (E : env) -> (t : trm) -> okt E -> wft E (typ_sel t) -> sub E (typ_sel t) (typ_sel t)
    | sub_sel1 : (E : env) -> (U : typ) -> (t : trm) ->
        has E t (typ_mem false U) -> sub E (typ_sel t) U
    | sub_sel2 : (E : env) -> (S : typ) -> (t : trm) ->
        has E t (typ_mem true S) -> sub E S (typ_sel t)
    | sub_mem_false : (E : env) -> (b1 : Bool) -> (T1 T2 : typ) ->
        sub E T1 T2 -> sub E (typ_mem b1 T1) (typ_mem false T2)
    | sub_mem_true : (E : env) -> (T1 T2 : typ) ->
        sub E T1 T2 -> sub E T2 T1 -> sub E (typ_mem true T1) (typ_mem true T2)
    | sub_all : (L : Vars) -> (E : env) -> (S1 S2 T1 T2 : typ) ->
        sub E T1 S1 ->
        (∀ (x : Var), x ∉ L -> sub ((x, T1) :: E) (S2 open_t_var x) (T2 open_t_var x)) ->
        sub E (typ_all S1 S2) (typ_all T1 T2)
    | sub_trans : (E : env) -> (S T U : typ) -> sub E S T -> sub E T U -> sub E S U

  inductive has : env -> trm -> typ -> Prop where
    | has_var : (E : env) -> (x : Var) -> (T : typ) -> okt E -> binds x T E -> has E (trm_fvar x) T
    | has_mem : (E : env) -> (b : Bool) -> (T : typ) -> okt E -> wft E T -> has E (trm_mem T) (typ_mem b T)
    | has_abs : (E : env) -> (V : typ) -> (e : trm) -> (T : typ) ->
        okt E -> wfe E (trm_abs V e) -> wft E (typ_all V T) ->
        has E (trm_abs V e) (typ_all V T)
    | has_sub : (E : env) -> (t : trm) -> (T U : typ) -> has E t T -> sub E T U -> has E t U
end

/-- [Coq L208-238] Typing -/ 
inductive typing : env -> trm -> typ -> Prop where
  | typing_var : (E : env) -> (x : Var) -> (T : typ) -> okt E -> binds x T E -> typing E (trm_fvar x) T
  | typing_abs : (L : Vars) -> (E : env) -> (V : typ) -> (e1 : trm) -> (T1 : typ) ->
      (∀ (x : Var), x ∉ L -> typing ((x, V) :: E) (e1 open_e_var x) (T1 open_t_var x)) ->
      typing E (trm_abs V e1) (typ_all V T1)
  | typing_mem : (E : env) -> (T1 : typ) -> okt E -> wft E T1 -> typing E (trm_mem T1) (typ_mem true T1)
  | typing_app : (T1 : typ) -> (E : env) -> (e1 e2 : trm) -> (T2 : typ) ->
      typing E e1 (typ_all T1 T2) -> typing E e2 T1 -> wft E T2 -> typing E (trm_app e1 e2) T2
  | typing_appvar : (T1 : typ) -> (E : env) -> (e1 e2 : trm) -> (T2 T2' : typ) -> (M : typ) ->
      typing E e1 (typ_all T1 T2) -> typing E e2 T1 -> has E e2 M ->
      T2' = open_t T2 e2 -> wft E T2' -> typing E (trm_app e1 e2) T2'
  | typing_sub : (S : typ) -> (E : env) -> (e : trm) -> (T : typ) -> typing E e S -> sub E S T -> typing E e T

/-- [Coq L242-255] Reduction -/ 
inductive red : trm -> trm -> Prop where
  | red_app_1 : (e1 e1' e2 : trm) -> def_term e2 -> red e1 e1' -> red (trm_app e1 e2) (trm_app e1' e2)
  | red_app_2 : (e1 e2 e2' : trm) -> value e1 -> red e2 e2' -> red (trm_app e1 e2) (trm_app e1 e2')
  | red_abs : (V : typ) -> (e1 : trm) -> (v2 : trm) -> def_term (trm_abs V e1) -> value v2 -> red (trm_app (trm_abs V e1) v2) (open_e e1 v2)

/-- [Coq L258-266] -/ 
@[simp] def preservation : Prop := ∀ (e e' : trm) (T : typ), typing [] e T -> red e e' -> typing [] e' T
@[simp] def progress : Prop := ∀ (e : trm) (T : typ), typing [] e T -> value e ∨ (∃ e', red e e')

/-- [Coq L277-283, 285-294] fv (mutual) -/ 
mutual
  @[simp] def fv_t (T : typ) : Vars :=
    match T with
    | typ_top           => ∅
    | typ_sel t         => fv_e t
    | typ_mem _ T1      => fv_t T1
    | typ_all T1 T2     => (fv_t T1) ∪ (fv_t T2)

  @[simp] def fv_e (e : trm) : Vars :=
    match e with
    | trm_bvar _        => ∅
    | trm_fvar x        => {x}
    | trm_abs V e1      => (fv_t V) ∪ (fv_e e1)
    | trm_mem T         => fv_t T
    | trm_app e1 e2     => (fv_e e1) ∪ (fv_e e2)
end

/-- [Coq L298-305, 308-315] substitution (mutual) -/ 
mutual
  @[simp] def subst_t (z : Var) (u : trm) (T : typ) : typ :=
    match T with
    | typ_top           => typ_top
    | typ_sel t         => typ_sel (subst_e z u t)
    | typ_mem b T1      => typ_mem b (subst_t z u T1)
    | typ_all T1 T2     => typ_all (subst_t z u T1) (subst_t z u T2)
  
  @[simp] def subst_e (z : Var) (u : trm) (e : trm) : trm :=
    match e with
    | trm_bvar i        => trm_bvar i
    | trm_fvar x        => by
        classical
        exact (if h : x = z then (by simpa [h] using u) else trm_fvar x)
    | trm_abs V e1      => trm_abs (subst_t z u V) (subst_e z u e1)
    | trm_mem T1        => trm_mem (subst_t z u T1)
    | trm_app e1 e2     => trm_app (subst_e z u e1) (subst_e z u e2)
end

end Lp2lc.Active.Dsub
