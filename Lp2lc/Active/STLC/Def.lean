import Mathlib.Tactic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.STLC

-- Basic types --
inductive Typ : Type
| typ_all : Typ -- all-inclusive base type
| typ_arrow : Typ → Typ → Typ
deriving DecidableEq, Repr

-- Defining (pre)terms by recursion --
inductive Trm : Type
| bvar : Nat → Trm
| fvar : Var → Trm
| abs : Typ → Trm → Trm
| app : Trm → Trm → Trm
deriving DecidableEq, Repr

namespace Trm

-- Notations --
notation t1 " -> " t2 => Typ.typ_arrow t1 t2
notation "€" i => bvar i
notation "$" x => fvar x
notation "λ " T "," t => abs T t
notation t1 " @ " t2 => app t1 t2

-- Defining free variable substitution by induction on terms --
@[simp]
def subst (x : Var) (a : Trm) : Trm → Trm
| bvar i => bvar i
| fvar y => if y = x then a else (fvar y)
| abs T u => abs T (subst x a u)
| app u1 u2 => app (subst x a u1) (subst x a u2)

notation  "["x" // "u"] "t => subst x u t

-- Set of free variables --
def fv : Trm → Finset Var
| bvar _ => {}
| fvar y => {y}
| abs _ t => fv t
| app t1 t2 => (fv t1) ∪ (fv t2)

--We can always pick a fresh variable for a given term out of a fixed set.

@[simp]
def opening (k : Nat) (u : Trm) : Trm → Trm
| bvar i => if k = i then u else (bvar i)
| fvar x => fvar x
| abs T t => abs T (opening (k + 1) u t)
| app t1 t2 => app (opening k u t1) (opening k u t2)

notation " {" k " ~> " u "} " t => opening k u t

--Opening at index zero
def open₀ (t : Trm) (u : Trm) : Trm := opening 0 u t

@[simp]
def closing (k : Nat) (x : Var) : Trm → Trm
| bvar i => bvar i
| fvar i => if x = i then (bvar k) else (fvar i)
| abs T t => abs T (closing (k + 1) x t)
| app t1 t2 => app (closing k x t1) (closing k x t2)

notation " { " k " <~ " x " } " t => closing k x t

--Closing at index zero
def close₀ (u : Trm) (x : Var) : Trm := closing 0 x u

inductive lc : Trm → Prop
| lc_var : ∀ x : Var, lc (fvar x)
| lc_abs : ∀ t : Trm, ∀ T : Typ, ∀ L : Finset Var,
    (∀ x : Var, x ∉ L → lc (open₀ t ($ x))) → lc (abs T t)
| lc_app : ∀ t1 t2 : Trm, lc t1 → lc t2 → lc (app t1 t2)


/-The predicate “body t” asserts that t describes
the body of a locally closed abstraction.-/
def body (t : Trm) : Prop := ∃ (L : Finset Var), ∀ x : Var, x ∉ L → lc (open₀ t ($ x))

end Trm

inductive Bind : Type where
  | bind_typ : Typ -> Bind --typing assumption

@[simp]
def Bind.unbox_typ : Bind → Typ
| Bind.bind_typ T => T

/-
In order to make typing judgments, we need the notion of Env.
The definition is designed to talk about "(x : T)"-like assumptions.
-/
notation "Env" => List (Var × Bind)

@[simp]
def context_terms : Env → (Finset Var)
| [] => ∅
| ((x, _) :: Γ') => {x} ∪ (context_terms Γ')

@[simp]
def in_context (x : Var) : Env → Prop
| [] => False
| (b :: m) => (x = b.1) ∨ (in_context x m)

inductive valid_ctx : Env → Prop where
| valid_nil : valid_ctx []
| valid_cons (Γ : Env) (x : Var) (T : Typ) :
    (valid_ctx Γ) → (¬ (in_context x Γ)) → valid_ctx ((x, Bind.bind_typ T) :: Γ)


--Properties of valid contexts
@[simp]
def get (x : Var) : Env → Option Typ
| [] => none
| (y , S) :: Γ' =>
    if x = y then
      some (Bind.unbox_typ S)
    else
      get x Γ'

@[simp]
def binds (x : Var) (T : Typ) (Γ : Env) : Prop := (get x Γ = some T)

class StldDirectDef(preTyp preTrm bind : Type) where
  env : Type
  trm_subst : Var → Trm → Trm → Trm
  trm_fv : Trm → Finset Var
  bind_unbox_typ : Bind → Typ
  env_context_terms : Env → Finset Var
  env_in_context : Var → Env → Prop
  env_get : Var → Env → Option Typ
  env_binds : Var → Typ → Env → Prop
  trm_opening : Nat → Trm → Trm → Trm
  trm_open0 : Trm → Trm → Trm
  trm_closing : Nat → Var → Trm → Trm
  trm_close0 : Trm → Var → Trm
  trm_body : Trm → Prop


open Trm

/- # Different Forms of β-reductions -/

--full beta reduction
inductive beta_red : Trm → Trm → Prop
| br_beta : ∀ (t1 : Trm) (t2 : Trm) (T : Typ), lc (abs T t1) → lc t2 → beta_red (app (abs T t1) t2) (open₀ t1 t2)
| br_app1 : ∀ (t1 : Trm) (t1' : Trm) (t2 : Trm), lc t2 → beta_red t1 t1' → beta_red (app t1 t2) (app t1' t2)
| br_app2 : ∀ (t1 : Trm) (t2 : Trm) (t2' : Trm), lc t1 → beta_red t2 t2' → beta_red (app t1 t2) (app t1 t2')
| br_abs : ∀ (t1 : Trm) (t1' : Trm) (T : Typ) (L : Finset Var),
    (∀ x : Var, x ∉ L → beta_red (open₀ t1 ($ x)) (open₀ t1' ($ x))) → beta_red (abs T t1) (abs T t1')


inductive para : Trm → Trm → Prop
| para_var : ∀ (x : Var), para ($ x) ($ x)
| para_red : ∀ (t1 : Trm) (t1' : Trm) (t2 : Trm) (t2' : Trm) (T : Typ) (L : Finset Var),
    (∀ x : Var, x ∉ L → para (open₀ t1 ($ x)) (open₀ t1' ($ x))) →
    para t2 t2' →
    para (app (abs T t1) t2) (open₀ t1' t2')
| para_app : ∀ (t1 : Trm) (t1' : Trm) (t2 : Trm) (t2' : Trm), para t1 t1' → para t2 t2' → para (app t1 t2) (app t1' t2')
| para_abs : ∀ (t1 : Trm) (t1' : Trm) (T : Typ) (L : Finset Var) ,
    (∀ x : Var, x ∉ L → para (open₀ t1 ($ x)) (open₀ t1' ($ x))) →
    para (abs T t1) (abs T t1')


inductive multi_red : Trm → Trm → Prop
| mr_refl : ∀ (t : Trm), lc t → multi_red t t
| mr_head : ∀ (t1 : Trm) (t2 : Trm) (t3 : Trm), (multi_red t1 t2) → beta_red t2 t3 → multi_red t1 t3


inductive multi_para : Trm → Trm → Prop
| m_para_refl : ∀ (t : Trm), lc t → multi_para t t
| m_para_head : ∀ (t1 : Trm) (t2 : Trm) (t3 : Trm), (multi_para t1 t2) → para t2 t3 → multi_para t1 t3


--Typing judgment
inductive typing : Env → Trm → Typ → Prop
| typ_var (Γ : Env) (x : Var) (T : Typ) : (valid_ctx Γ) → (binds x T Γ) → (typing Γ ($ x) T)
| typ_abs (L : Finset Var) (Γ : Env) (t : Trm) (T1 T2 : Typ) :
        ((x : Var) → x ∉ L → (typing ((x, Bind.bind_typ T1) :: Γ) (open₀ t ($ x)) T2)) → (typing Γ (abs T1 t) (Typ.typ_arrow T1 T2))
| typ_app (Γ : Env) (t₁ t₂ : Trm) (T1 T2 : Typ) :
        (typing Γ t₁ (Typ.typ_arrow T1 T2)) → (typing Γ t₂ T1) → typing Γ (app t₁ t₂) T2


--Typing judgments only allow valid contexts.

inductive value : Trm → Prop
| value_abs : ∀ (e : Trm) (T : Typ), lc (abs T e) → value (abs T e)


inductive eval : Trm → Trm → Prop
| eval_beta : ∀ (e1 : Trm) (e2 : Trm) (T : Typ), lc (abs T e1) → value e2 → eval (app (abs T e1) e2) (open₀ e1 e2)
| eval_app1 : ∀ (e1 : Trm) (e1' : Trm) (e2 : Trm), lc e2 → eval e1 e1' → eval (app e1 e2) (app e1' e2)
| eval_app2 : ∀ (e1 : Trm) (e2 : Trm) (e2' : Trm), lc e1 → eval e2 e2' → eval (app e1 e2) (app e1 e2')


end Lp2lc.Active.STLC
