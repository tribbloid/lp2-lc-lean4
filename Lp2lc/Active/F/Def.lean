import Mathlib.Tactic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.F

inductive Typ : Type where
  | bvar : Nat -> Typ
  | fvar : Var -> Typ
  | arrow : Typ -> Typ -> Typ
  | all : Typ -> Typ
deriving DecidableEq, Repr

inductive Trm : Type where
  | bvar : Nat -> Trm
  | fvar : Var -> Trm
  | abs : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm
  | tabs : Trm -> Trm
  | tapp : Trm -> Typ -> Trm
deriving DecidableEq, Repr

namespace Ops

@[simp]
def subst_fvar {a : Type} (mk : Var -> a) (x : Var) (u : a) (y : Var) : a :=
  if y = x then u else mk y

@[simp]
def open_bvar {a : Type} (mk : Nat -> a) (k i : Nat) (u : a) : a :=
  if k = i then u else mk i

@[simp]
def close_fvar {a : Type} (mk_bvar : Nat -> a) (mk_fvar : Var -> a) (k : Nat) (x y : Var) : a :=
  if x = y then mk_bvar k else mk_fvar y

end Ops

namespace Typ

@[simp]
def subst (X : Var) (U : Typ) : Typ -> Typ
  | Typ.bvar i => Typ.bvar i
  | Typ.fvar Y => Ops.subst_fvar Typ.fvar X U Y
  | Typ.arrow T1 T2 => Typ.arrow (subst X U T1) (subst X U T2)
  | Typ.all T => Typ.all (subst X U T)

notation "[[" X " // " U "]] " T => subst X U T

def fv : Typ -> Finset Var
  | Typ.bvar _ => {}
  | Typ.fvar Y => {Y}
  | Typ.arrow T1 T2 => fv T1 ∪ fv T2
  | Typ.all T => fv T

@[simp]
def opening (k : Nat) (U : Typ) : Typ -> Typ
  | Typ.bvar i => Ops.open_bvar Typ.bvar k i U
  | Typ.fvar X => Typ.fvar X
  | Typ.arrow T1 T2 => Typ.arrow (opening k U T1) (opening k U T2)
  | Typ.all T => Typ.all (opening (k + 1) U T)

def open0 (T U : Typ) : Typ := opening 0 U T

@[simp]
def closing (k : Nat) (X : Var) : Typ -> Typ
  | Typ.bvar i => Typ.bvar i
  | Typ.fvar Y => Ops.close_fvar Typ.bvar Typ.fvar k X Y
  | Typ.arrow T1 T2 => Typ.arrow (closing k X T1) (closing k X T2)
  | Typ.all T => Typ.all (closing (k + 1) X T)

def close0 (T : Typ) (X : Var) : Typ := closing 0 X T

inductive lc : Typ -> Prop where
  | lc_fvar : forall X : Var, lc (Typ.fvar X)
  | lc_arrow : forall T1 T2 : Typ, lc T1 -> lc T2 -> lc (Typ.arrow T1 T2)
  | lc_all : forall T : Typ, forall L : Finset Var,
      (forall X : Var, X ∉ L -> lc (open0 T (Typ.fvar X))) -> lc (Typ.all T)

def body (T : Typ) : Prop :=
  exists L : Finset Var, forall X : Var, X ∉ L -> lc (open0 T (Typ.fvar X))

end Typ

namespace Trm

notation "$" x => Trm.fvar x
notation "lam " T ", " t => Trm.abs T t
notation t1 " @ " t2 => Trm.app t1 t2
notation "tabs " t => Trm.tabs t
notation "tapp " t " [" T "]" => Trm.tapp t T

@[simp]
def subst_ee (x : Var) (u : Trm) : Trm -> Trm
  | Trm.bvar i => Trm.bvar i
  | Trm.fvar y => Ops.subst_fvar Trm.fvar x u y
  | Trm.abs T t => Trm.abs T (subst_ee x u t)
  | Trm.app t1 t2 => Trm.app (subst_ee x u t1) (subst_ee x u t2)
  | Trm.tabs t => Trm.tabs (subst_ee x u t)
  | Trm.tapp t T => Trm.tapp (subst_ee x u t) T

notation "[" x " // " u "] " t => subst_ee x u t

@[simp]
def subst_te (X : Var) (U : Typ) : Trm -> Trm
  | Trm.bvar i => Trm.bvar i
  | Trm.fvar y => Trm.fvar y
  | Trm.abs T t => Trm.abs (Typ.subst X U T) (subst_te X U t)
  | Trm.app t1 t2 => Trm.app (subst_te X U t1) (subst_te X U t2)
  | Trm.tabs t => Trm.tabs (subst_te X U t)
  | Trm.tapp t T => Trm.tapp (subst_te X U t) (Typ.subst X U T)

def fv_ee : Trm -> Finset Var
  | Trm.bvar _ => {}
  | Trm.fvar y => {y}
  | Trm.abs _ t => fv_ee t
  | Trm.app t1 t2 => fv_ee t1 ∪ fv_ee t2
  | Trm.tabs t => fv_ee t
  | Trm.tapp t _ => fv_ee t

def fv_te : Trm -> Finset Var
  | Trm.bvar _ => {}
  | Trm.fvar _ => {}
  | Trm.abs T t => Typ.fv T ∪ fv_te t
  | Trm.app t1 t2 => fv_te t1 ∪ fv_te t2
  | Trm.tabs t => fv_te t
  | Trm.tapp t T => fv_te t ∪ Typ.fv T

@[simp]
def opening_ee (k : Nat) (u : Trm) : Trm -> Trm
  | Trm.bvar i => Ops.open_bvar Trm.bvar k i u
  | Trm.fvar x => Trm.fvar x
  | Trm.abs T t => Trm.abs T (opening_ee (k + 1) u t)
  | Trm.app t1 t2 => Trm.app (opening_ee k u t1) (opening_ee k u t2)
  | Trm.tabs t => Trm.tabs (opening_ee k u t)
  | Trm.tapp t T => Trm.tapp (opening_ee k u t) T

def open_ee0 (t : Trm) (u : Trm) : Trm := opening_ee 0 u t

@[simp]
def opening_te (k : Nat) (U : Typ) : Trm -> Trm
  | Trm.bvar i => Trm.bvar i
  | Trm.fvar x => Trm.fvar x
  | Trm.abs T t => Trm.abs (Typ.opening k U T) (opening_te k U t)
  | Trm.app t1 t2 => Trm.app (opening_te k U t1) (opening_te k U t2)
  | Trm.tabs t => Trm.tabs (opening_te (k + 1) U t)
  | Trm.tapp t T => Trm.tapp (opening_te k U t) (Typ.opening k U T)

def open_te0 (t : Trm) (U : Typ) : Trm := opening_te 0 U t

@[simp]
def closing_ee (k : Nat) (x : Var) : Trm -> Trm
  | Trm.bvar i => Trm.bvar i
  | Trm.fvar y => Ops.close_fvar Trm.bvar Trm.fvar k x y
  | Trm.abs T t => Trm.abs T (closing_ee (k + 1) x t)
  | Trm.app t1 t2 => Trm.app (closing_ee k x t1) (closing_ee k x t2)
  | Trm.tabs t => Trm.tabs (closing_ee k x t)
  | Trm.tapp t T => Trm.tapp (closing_ee k x t) T

def close_ee0 (t : Trm) (x : Var) : Trm := closing_ee 0 x t

@[simp]
def closing_te (k : Nat) (X : Var) : Trm -> Trm
  | Trm.bvar i => Trm.bvar i
  | Trm.fvar x => Trm.fvar x
  | Trm.abs T t => Trm.abs (Typ.closing k X T) (closing_te k X t)
  | Trm.app t1 t2 => Trm.app (closing_te k X t1) (closing_te k X t2)
  | Trm.tabs t => Trm.tabs (closing_te (k + 1) X t)
  | Trm.tapp t T => Trm.tapp (closing_te k X t) (Typ.closing k X T)

def close_te0 (t : Trm) (X : Var) : Trm := closing_te 0 X t

inductive lc : Trm -> Prop where
  | lc_var : forall x : Var, lc (Trm.fvar x)
  | lc_abs : forall t : Trm, forall T : Typ, forall L : Finset Var,
      Typ.lc T ->
      (forall x : Var, x ∉ L -> lc (open_ee0 t (Trm.fvar x))) -> lc (Trm.abs T t)
  | lc_app : forall t1 t2 : Trm, lc t1 -> lc t2 -> lc (Trm.app t1 t2)
  | lc_tabs : forall t : Trm, forall L : Finset Var,
      (forall X : Var, X ∉ L -> lc (open_te0 t (Typ.fvar X))) -> lc (Trm.tabs t)
  | lc_tapp : forall t : Trm, forall T : Typ, lc t -> Typ.lc T -> lc (Trm.tapp t T)

def body_ee (t : Trm) : Prop :=
  exists L : Finset Var, forall x : Var, x ∉ L -> lc (open_ee0 t (Trm.fvar x))

def body_te (t : Trm) : Prop :=
  exists L : Finset Var, forall X : Var, X ∉ L -> lc (open_te0 t (Typ.fvar X))

end Trm

inductive Bind : Type where
  | bind_tvar : Bind
  | bind_typ : Typ -> Bind
deriving DecidableEq, Repr

notation "Env" => List (Var × Bind)

@[simp]
def context_terms : Env -> Finset Var
  | [] => ∅
  | (x, _) :: Gamma' => {x} ∪ context_terms Gamma'

@[simp]
def in_context (x : Var) (Gamma : Env) : Prop := x ∈ context_terms Gamma

inductive valid_ctx : Env -> Prop where
  | valid_nil : valid_ctx []
  | valid_tvar (Gamma : Env) (X : Var) :
      valid_ctx Gamma -> ¬ in_context X Gamma -> valid_ctx ((X, Bind.bind_tvar) :: Gamma)
  | valid_typ (Gamma : Env) (x : Var) (T : Typ) :
      valid_ctx Gamma -> Typ.lc T -> ¬ in_context x Gamma -> valid_ctx ((x, Bind.bind_typ T) :: Gamma)

@[simp]
def get_typ (x : Var) : Env -> Option Typ
  | [] => none
  | (y, b) :: Gamma' =>
      if x = y then
        match b with
        | Bind.bind_typ T => some T
        | Bind.bind_tvar => none
      else
        get_typ x Gamma'

@[simp]
def binds (x : Var) (T : Typ) (Gamma : Env) : Prop := get_typ x Gamma = some T

open Trm

inductive typing : Env -> Trm -> Typ -> Prop where
  | typ_var (Gamma : Env) (x : Var) (T : Typ) :
      valid_ctx Gamma ->
      binds x T Gamma ->
      typing Gamma (Trm.fvar x) T
  | typ_abs (L : Finset Var) (Gamma : Env) (t : Trm) (T1 T2 : Typ) :
      Typ.lc T1 ->
      (forall x : Var, x ∉ L -> typing ((x, Bind.bind_typ T1) :: Gamma) (Trm.open_ee0 t (Trm.fvar x)) T2) ->
      typing Gamma (Trm.abs T1 t) (Typ.arrow T1 T2)
  | typ_app (Gamma : Env) (t1 t2 : Trm) (T1 T2 : Typ) :
      typing Gamma t1 (Typ.arrow T1 T2) ->
      typing Gamma t2 T1 ->
      typing Gamma (Trm.app t1 t2) T2
  | typ_tabs (L : Finset Var) (Gamma : Env) (t : Trm) (T : Typ) :
      (forall X : Var, X ∉ L ->
        typing ((X, Bind.bind_tvar) :: Gamma) (Trm.open_te0 t (Typ.fvar X)) (Typ.open0 T (Typ.fvar X))) ->
      typing Gamma (Trm.tabs t) (Typ.all T)
  | typ_tapp (Gamma : Env) (t : Trm) (T U : Typ) :
      typing Gamma t (Typ.all U) ->
      Typ.lc T ->
      typing Gamma (Trm.tapp t T) (Typ.open0 U T)

inductive value : Trm -> Prop where
  | value_abs : forall e : Trm, forall T : Typ, Trm.lc (Trm.abs T e) -> value (Trm.abs T e)
  | value_tabs : forall e : Trm, Trm.lc (Trm.tabs e) -> value (Trm.tabs e)

inductive eval : Trm -> Trm -> Prop where
  | eval_beta : forall e1 e2 : Trm, forall T : Typ,
      Trm.lc (Trm.abs T e1) ->
      value e2 ->
      eval (Trm.app (Trm.abs T e1) e2) (Trm.open_ee0 e1 e2)
  | eval_tbeta : forall e1 : Trm, forall T : Typ,
      Trm.lc (Trm.tabs e1) ->
      Typ.lc T ->
      eval (Trm.tapp (Trm.tabs e1) T) (Trm.open_te0 e1 T)
  | eval_app1 : forall e1 e1' e2 : Trm,
      Trm.lc e2 ->
      eval e1 e1' ->
      eval (Trm.app e1 e2) (Trm.app e1' e2)
  | eval_app2 : forall e1 e2 e2' : Trm,
      Trm.lc e1 ->
      eval e2 e2' ->
      eval (Trm.app e1 e2) (Trm.app e1 e2')
  | eval_tapp : forall e1 e1' : Trm, forall T : Typ,
      Typ.lc T ->
      eval e1 e1' ->
      eval (Trm.tapp e1 T) (Trm.tapp e1' T)

end Lp2lc.Active.F
