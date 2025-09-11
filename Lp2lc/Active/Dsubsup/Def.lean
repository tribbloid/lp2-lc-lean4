import Std
import Mathlib.Data.Finset.Basic
import Aesop
import «Lp2lc».Shared

namespace Lp2lc.Active.Dsubsup

-- Coq source: Lp2lc_coq/Active/Dsubsup.v
-- Auto-scaffolded: definitions and judgments. Proofs are left as sorry (see Proof.lean).

mutual
  -- [Coq L24-29, L33-38]
  inductive typ : Type where
    | typ_bot   : typ
    | typ_top   : typ
    | typ_sel   : trm -> typ
    | typ_mem   : typ -> typ -> typ
    | typ_all   : typ -> typ -> typ
    deriving BEq, DecidableEq

  inductive trm : Type where
    | trm_bvar : Nat -> trm
    | trm_fvar : Var -> trm
    | trm_abs  : typ -> trm -> trm
    | trm_mem  : typ -> trm
    | trm_app  : trm -> trm -> trm
    deriving BEq, DecidableEq
end

open typ trm

-- [Coq L40-58] Opening operations (mutual)
mutual
  partial def open_t_rec (k : Nat) (f : trm) (T : typ) : typ :=
    match T with
    | typ_bot           => typ_bot
    | typ_top           => typ_top
    | typ_sel t         => typ_sel (open_e_rec k f t)
    | typ_mem T1 T2     => typ_mem (open_t_rec k f T1) (open_t_rec k f T2)
    | typ_all T1 T2     => typ_all (open_t_rec k f T1) (open_t_rec (k + 1) f T2)

  partial def open_e_rec (k : Nat) (f : trm) (e : trm) : trm :=
    match e with
    | trm_bvar i        => if k = i then f else (trm_bvar i)
    | trm_fvar x        => trm_fvar x
    | trm_abs V e1      => trm_abs (open_t_rec k f V) (open_e_rec (k + 1) f e1)
    | trm_mem T         => trm_mem (open_t_rec k f T)
    | trm_app e1 e2     => trm_app (open_e_rec k f e1) (open_e_rec k f e2)
end

@[simp] def open_t (T : typ) (f : trm) : typ := open_t_rec 0 f T
@[simp] def open_e (t : trm) (u : trm) : trm := open_e_rec 0 u t

-- [Coq L65-67] Notations
notation:67 T " open_t_var " x => open_t T (trm_fvar x)
notation:67 t " open_e_var " x => open_e t (trm_fvar x)

-- [Coq L70-102] Local closure (mutual)
mutual
  inductive def_type : typ -> Prop where
    | type_bot : def_type typ_bot
    | type_top : def_type typ_top
    | type_sel : (e1 : trm) -> def_term e1 -> def_type (typ_sel e1)
    | type_mem : (T1 T2 : typ) -> def_type T1 -> def_type T2 -> def_type (typ_mem T1 T2)
    | type_all : (L : Vars) -> (T1 T2 : typ) -> def_type T1 -> (∀ x, x ∉ L -> def_type (open_t T2 (trm_fvar x))) -> def_type (typ_all T1 T2)

  inductive def_term : trm -> Prop where
    | term_var : (x : Var) -> def_term (trm_fvar x)
    | term_abs : (L : Vars) -> (V : typ) -> (e1 : trm) -> def_type V -> (∀ x, x ∉ L -> def_term (open_e e1 (trm_fvar x))) -> def_term (trm_abs V e1)
    | term_mem : (T1 : typ) -> def_type T1 -> def_term (trm_mem T1)
    | term_app : (e1 e2 : trm) -> def_term e1 -> def_term e2 -> def_term (trm_app e1 e2)
end

-- [Coq L106-110] Values
inductive value : trm -> Prop where
  | value_abs  : (V : typ) -> (e1 : trm) -> def_term (trm_abs V e1) -> value (trm_abs V e1)
  | value_mem  : (V : typ) -> def_term (trm_mem V) -> value (trm_mem V)

-- [Coq L114] Environment as list of type bindings
abbrev env := List (Var × typ)

namespace Env
  def dom (E : env) : Vars := Lp2lc.Active.Env.domOf E
end Env

-- [Coq L126, 140] binds helper
@[simp] def binds (x : Var) (U : typ) (E : env) : Prop := E.lookup x = some U

-- [Coq L121-154, 155-175] Well-formedness (mutual)
mutual
  inductive wft : env -> typ -> Prop where
    | wft_bot : (E : env) -> wft E typ_bot
    | wft_top : (E : env) -> wft E typ_top
    | wft_sel : (E : env) -> (e : trm) -> (value e ∨ ∃ x, trm_fvar x = e) -> wfe E e -> wft E (typ_sel e)
    | wft_mem : (E : env) -> (T1 T2 : typ) -> wft E T1 -> wft E T2 -> wft E (typ_mem T1 T2)
    | wft_all : (L : Vars) -> (E : env) -> (T1 T2 : typ) -> wft E T1 -> (∀ x, x ∉ L -> wft ((x, T1) :: E) (open_t T2 (trm_fvar x))) -> wft E (typ_all T1 T2)

  inductive wfe : env -> trm -> Prop where
    | wfe_var : (U : typ) -> (E : env) -> (x : Var) -> binds x U E -> wfe E (trm_fvar x)
    | wfe_abs : (L : Vars) -> (E : env) -> (V : typ) -> (e : trm) -> wft E V -> (∀ x, x ∉ L -> wfe ((x, V) :: E) (open_e e (trm_fvar x))) -> wfe E (trm_abs V e)
    | wfe_mem : (E : env) -> (T : typ) -> wft E T -> wfe E (trm_mem T)
    | wfe_app : (E : env) -> (e1 e2 : trm) -> wfe E e1 -> wfe E e2 -> wfe E (trm_app e1 e2)
end

-- [Coq L181-185] okt env
inductive okt : env -> Prop where
  | okt_empty : okt []
  | okt_push : (E : env) -> (x : Var) -> (T : typ) -> okt E -> wft E T -> E.lookup x = none -> okt ((x, T) :: E)

-- [Coq L168-199, 200-214] Subtyping and has (mutual)
mutual
  inductive sub : env -> typ -> typ -> Prop where
    | sub_bot : (E : env) -> (T : typ) -> okt E -> wft E T -> sub E typ_bot T
    | sub_top : (E : env) -> (S : typ) -> okt E -> wft E S -> sub E S typ_top
    | sub_refl_sel : (E : env) -> (t : trm) -> okt E -> wft E (typ_sel t) -> sub E (typ_sel t) (typ_sel t)
    | sub_sel1 : (E : env) -> (S U : typ) -> (t : trm) -> has E t (typ_mem S U) -> sub E (typ_sel t) U
    | sub_sel2 : (E : env) -> (S U : typ) -> (t : trm) -> has E t (typ_mem S U) -> sub E S (typ_sel t)
    | sub_mem : (E : env) -> (S1 U1 S2 U2 : typ) -> sub E S2 S1 -> sub E U1 U2 -> sub E (typ_mem S1 U1) (typ_mem S2 U2)
    | sub_all : (L : Vars) -> (E : env) -> (S1 S2 T1 T2 : typ) ->
        sub E T1 S1 -> (∀ x, x ∉ L -> sub ((x, T1) :: E) (open_t S2 (trm_fvar x)) (open_t T2 (trm_fvar x))) -> sub E (typ_all S1 S2) (typ_all T1 T2)
    | sub_trans : (E : env) -> (S T U : typ) -> sub E S T -> sub E T U -> sub E S U

  inductive has : env -> trm -> typ -> Prop where
    | has_var : (E : env) -> (x : Var) -> (T : typ) -> okt E -> binds x T E -> has E (trm_fvar x) T
    | has_mem : (E : env) -> (T : typ) -> okt E -> wft E T -> has E (trm_mem T) (typ_mem T T)
    | has_abs : (E : env) -> (V : typ) -> (e : trm) -> (T : typ) -> okt E -> wfe E (trm_abs V e) -> wft E (typ_all V T) -> has E (trm_abs V e) (typ_all V T)
    | has_sub : (E : env) -> (t : trm) -> (T U : typ) -> has E t T -> sub E T U -> has E t U
end

-- [Coq L219-247] Typing
inductive typing : env -> trm -> typ -> Prop where
  | typing_var : (E : env) -> (x : Var) -> (T : typ) -> okt E -> binds x T E -> typing E (trm_fvar x) T
  | typing_abs : (L : Vars) -> (E : env) -> (V : typ) -> (e1 : trm) -> (T1 : typ) ->
      (∀ x, x ∉ L -> typing ((x, V) :: E) (open_e e1 (trm_fvar x)) (open_t T1 (trm_fvar x))) -> typing E (trm_abs V e1) (typ_all V T1)
  | typing_mem : (E : env) -> (T1 : typ) -> okt E -> wft E T1 -> typing E (trm_mem T1) (typ_mem T1 T1)
  | typing_app : (T1 : typ) -> (E : env) -> (e1 e2 : trm) -> (T2 : typ) -> typing E e1 (typ_all T1 T2) -> typing E e2 T1 -> wft E T2 -> typing E (trm_app e1 e2) T2
  | typing_appvar : (T1 : typ) -> (E : env) -> (e1 e2 : trm) -> (T2 T2' M : typ) ->
      typing E e1 (typ_all T1 T2) -> typing E e2 T1 -> has E e2 M ->
      T2' = open_t T2 e2 -> wft E T2' -> typing E (trm_app e1 e2) T2'
  | typing_sub : (S : typ) -> (E : env) -> (e : trm) -> (T : typ) -> typing E e S -> sub E S T -> typing E e T

-- [Coq L251-263] Reduction (term)
inductive red : trm -> trm -> Prop where
  | red_app_1 : (e1 e1' e2 : trm) -> def_term e2 -> red e1 e1' -> red (trm_app e1 e2) (trm_app e1' e2)
  | red_app_2 : (e1 e2 e2' : trm) -> value e1 -> red e2 e2' -> red (trm_app e1 e2) (trm_app e1 e2')
  | red_abs : (V : typ) -> (e1 : trm) -> (v2 : trm) -> def_term (trm_abs V e1) -> value v2 -> red (trm_app (trm_abs V e1) v2) (open_e e1 v2)

-- [Coq L267-275, 286-295] Meta goals
@[simp] def preservation : Prop := ∀ (e e' : trm) (T : typ), typing [] e T -> red e e' -> typing [] e' T
@[simp] def progress     : Prop := ∀ (e : trm) (T : typ), typing [] e T -> value e ∨ (∃ e', red e e')

-- [Coq L286-304] Free variables (mutual)
mutual
  @[simp] def fv_t (T : typ) : Vars :=
    match T with
    | typ_bot           => ∅
    | typ_top           => ∅
    | typ_sel t         => fv_e t
    | typ_mem T1 T2     => (fv_t T1) ∪ (fv_t T2)
    | typ_all T1 T2     => (fv_t T1) ∪ (fv_t T2)

  @[simp] def fv_e (e : trm) : Vars :=
    match e with
    | trm_bvar _        => ∅
    | trm_fvar x        => {x}
    | trm_abs V e1      => (fv_t V) ∪ (fv_e e1)
    | trm_mem T         => fv_t T
    | trm_app e1 e2     => (fv_e e1) ∪ (fv_e e2)
end

-- [Coq L308-326] Substitution (mutual)
mutual
  @[simp] def subst_t (z : Var) (u : trm) (T : typ) : typ :=
    match T with
    | typ_bot           => typ_bot
    | typ_top           => typ_top
    | typ_sel t         => typ_sel (subst_e z u t)
    | typ_mem T1 T2     => typ_mem (subst_t z u T1) (subst_t z u T2)
    | typ_all T1 T2     => typ_all (subst_t z u T1) (subst_t z u T2)

  @[simp] def subst_e (z : Var) (u : trm) (e : trm) : trm :=
    match e with
    | trm_bvar i        => trm_bvar i
    | trm_fvar x        => if x = z then u else (trm_fvar x)
    | trm_abs V e1      => trm_abs (subst_t z u V) (subst_e z u e1)
    | trm_mem T1        => trm_mem (subst_t z u T1)
    | trm_app e1 e2     => trm_app (subst_e z u e1) (subst_e z u e2)
end

end Lp2lc.Active.Dsubsup
