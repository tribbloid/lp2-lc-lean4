import Std
import Iris.Algebra.OFE

namespace Lp2lc.Active.STLC

structure Var where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

abbrev Vars := Finset Var

theorem var_fresh : (L : Vars) → ∃ X : Var, X ∉ L := by
  sorry

structure Later (A : Type u) : Type u where
  next :: car : A
  deriving DecidableEq, Repr

namespace Guarded

inductive Typ (Peer : Type _) : Type _ where
| typ_all : Typ Peer
| typ_arrow : Later Peer → Later Peer → Typ Peer

inductive Trm (Typ Peer : Type _) : Type _ where
| bvar : Nat → Trm Typ Peer
| fvar : Var → Trm Typ Peer
| abs : Typ → Later Peer → Trm Typ Peer
| app : Later Peer → Later Peer → Trm Typ Peer

end Guarded

inductive Typ : Type
| self : Guarded.Typ Typ → Typ

namespace Typ

@[match_pattern, simp]
abbrev typ_all : Typ := Typ.self Guarded.Typ.typ_all

@[match_pattern, simp]
abbrev typ_arrow (T1 T2 : Typ) : Typ := Typ.self (Guarded.Typ.typ_arrow (.next T1) (.next T2))

namespace typ_arrow

theorem injEq {T1 T2 S1 S2 : Typ} :
    Typ.typ_arrow T1 T2 = Typ.typ_arrow S1 S2 ↔ T1 = S1 ∧ T2 = S2 := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end typ_arrow

def size : Typ → Nat
  | Typ.self Guarded.Typ.typ_all => 1
  | Typ.self (Guarded.Typ.typ_arrow T1 T2) =>
      match T1, T2 with
      | ⟨T1⟩, ⟨T2⟩ => size T1 + size T2 + 1

end Typ

inductive Trm : Type
| self : Guarded.Trm Typ Trm → Trm

namespace Trm

@[match_pattern, simp]
abbrev bvar (i : Nat) : Trm := Trm.self (Guarded.Trm.bvar i)

@[match_pattern, simp]
abbrev fvar (x : Var) : Trm := Trm.self (Guarded.Trm.fvar x)

@[match_pattern, simp]
abbrev abs (T : Typ) (t : Trm) : Trm := Trm.self (Guarded.Trm.abs T (.next t))

@[match_pattern, simp]
abbrev app (t1 t2 : Trm) : Trm := Trm.self (Guarded.Trm.app (.next t1) (.next t2))

namespace bvar

theorem injEq {i j : Nat} : Trm.bvar i = Trm.bvar j ↔ i = j := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

end bvar

namespace fvar

theorem injEq {x y : Var} : Trm.fvar x = Trm.fvar y ↔ x = y := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

end fvar

namespace abs

theorem injEq {T1 T2 : Typ} {t1 t2 : Trm} :
    Trm.abs T1 t1 = Trm.abs T2 t2 ↔ T1 = T2 ∧ t1 = t2 := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end abs

namespace app

theorem injEq {t1 t2 u1 u2 : Trm} :
    Trm.app t1 t2 = Trm.app u1 u2 ↔ t1 = u1 ∧ t2 = u2 := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end app

def size : Trm → Nat
  | Trm.self (Guarded.Trm.bvar _) => 1
  | Trm.self (Guarded.Trm.fvar _) => 1
  | Trm.self (Guarded.Trm.abs _ t) =>
      match t with
      | ⟨t⟩ => size t + 1
  | Trm.self (Guarded.Trm.app t1 t2) =>
      match t1, t2 with
      | ⟨t1⟩, ⟨t2⟩ => size t1 + size t2 + 1

@[elab_as_elim]
def rec_like {motive : Trm → Sort _}
    (bvar : ∀ i, motive (Trm.bvar i))
    (fvar : ∀ x, motive (Trm.fvar x))
    (abs : ∀ T t, motive t → motive (Trm.abs T t))
    (app : ∀ t1 t2, motive t1 → motive t2 → motive (Trm.app t1 t2)) :
    ∀ t, motive t
  | Trm.self (Guarded.Trm.bvar i) => bvar i
  | Trm.self (Guarded.Trm.fvar x) => fvar x
  | Trm.self (Guarded.Trm.abs T t) =>
      by
        cases t
        exact abs T _ (rec_like bvar fvar abs app _)
  | Trm.self (Guarded.Trm.app t1 t2) =>
      by
        cases t1
        cases t2
        exact app _ _ (rec_like bvar fvar abs app _) (rec_like bvar fvar abs app _)
termination_by t => size t
decreasing_by
  all_goals
    first
      | cases t
      | cases t1; cases t2
    simp [size]

notation t1 " -> " t2 => Typ.typ_arrow t1 t2
notation "€" i => bvar i
notation "$" x => fvar x
notation "λ " T "," t => abs T t
notation t1 " @ " t2 => app t1 t2

def subst (x : Var) (a : Trm) : Trm → Trm
| bvar i => bvar i
| fvar y => if y = x then a else fvar y
| abs T u => abs T (subst x a u)
| app u1 u2 => app (subst x a u1) (subst x a u2)
termination_by t => size t
decreasing_by
  all_goals
    first
      | cases u
      | cases u1; cases u2
    simp [size]

notation "[" x " // " u "] " t => subst x u t

def fv : Trm → Finset Var
| bvar _ => {}
| fvar y => {y}
| abs _ t => fv t
| app t1 t2 => fv t1 ∪ fv t2
termination_by t => size t
decreasing_by
  all_goals
    first
      | cases t
      | cases t1; cases t2
    simp [size]

def opening (k : Nat) (u : Trm) : Trm → Trm
| bvar i => if k = i then u else bvar i
| fvar x => fvar x
| abs T t => abs T (opening (k + 1) u t)
| app t1 t2 => app (opening k u t1) (opening k u t2)
termination_by t => size t
decreasing_by
  all_goals
    first
      | cases t
      | cases t1; cases t2
    simp [size]

notation " {" k " ~> " u "} " t => opening k u t

def open₀ (t : Trm) (u : Trm) : Trm := opening 0 u t

def closing (k : Nat) (x : Var) : Trm → Trm
| bvar i => bvar i
| fvar i => if x = i then bvar k else fvar i
| abs T t => abs T (closing (k + 1) x t)
| app t1 t2 => app (closing k x t1) (closing k x t2)
termination_by t => size t
decreasing_by
  all_goals
    first
      | cases t
      | cases t1; cases t2
    simp [size]

notation " { " k " <~ " x " } " t => closing k x t

def close₀ (u : Trm) (x : Var) : Trm := closing 0 x u

inductive lc : Trm → Prop
| lc_var : ∀ x : Var, lc (fvar x)
| lc_abs : ∀ t : Trm, ∀ T : Typ, ∀ L : Finset Var,
    (∀ x : Var, x ∉ L → lc (open₀ t ($ x))) → lc (abs T t)
| lc_app : ∀ t1 t2 : Trm, lc t1 → lc t2 → lc (app t1 t2)

def body (t : Trm) : Prop := ∃ (L : Finset Var), ∀ x : Var, x ∉ L → lc (open₀ t ($ x))

end Trm

abbrev Env := List (Var × Typ)

namespace Env

@[simp]
def terms : Env → Finset Var
| [] => ∅
| (x, _) :: Γ' => {x} ∪ terms Γ'

@[simp]
def in_context (x : Var) : Env → Prop
| [] => False
| b :: m => x = b.1 ∨ in_context x m

inductive valid_ctx : Env → Prop where
| valid_nil : valid_ctx []
| valid_cons (Γ : Env) (x : Var) (T : Typ) :
    valid_ctx Γ → ¬ in_context x Γ → valid_ctx ((x, T) :: Γ)

@[simp]
def get (x : Var) : Env → Option Typ
| [] => none
| (y, S) :: Γ' =>
    if x = y then
      some S
    else
      get x Γ'

@[simp]
def binds (x : Var) (T : Typ) (Γ : Env) : Prop := get x Γ = some T

end Env

open Trm

inductive beta_red : Trm → Trm → Prop
| br_beta : ∀ (t1 : Trm) (t2 : Trm) (T : Typ),
    lc (abs T t1) → lc t2 → beta_red (app (abs T t1) t2) (open₀ t1 t2)
| br_app1 : ∀ (t1 : Trm) (t1' : Trm) (t2 : Trm),
    lc t2 → beta_red t1 t1' → beta_red (app t1 t2) (app t1' t2)
| br_app2 : ∀ (t1 : Trm) (t2 : Trm) (t2' : Trm),
    lc t1 → beta_red t2 t2' → beta_red (app t1 t2) (app t1 t2')
| br_abs : ∀ (t1 : Trm) (t1' : Trm) (T : Typ) (L : Finset Var),
    (∀ x : Var, x ∉ L → beta_red (open₀ t1 ($ x)) (open₀ t1' ($ x))) →
    beta_red (abs T t1) (abs T t1')

inductive para : Trm → Trm → Prop
| para_var : ∀ (x : Var), para ($ x) ($ x)
| para_red : ∀ (t1 : Trm) (t1' : Trm) (t2 : Trm) (t2' : Trm) (T : Typ) (L : Finset Var),
    (∀ x : Var, x ∉ L → para (open₀ t1 ($ x)) (open₀ t1' ($ x))) →
    para t2 t2' →
    para (app (abs T t1) t2) (open₀ t1' t2')
| para_app : ∀ (t1 : Trm) (t1' : Trm) (t2 : Trm) (t2' : Trm),
    para t1 t1' → para t2 t2' → para (app t1 t2) (app t1' t2')
| para_abs : ∀ (t1 : Trm) (t1' : Trm) (T : Typ) (L : Finset Var),
    (∀ x : Var, x ∉ L → para (open₀ t1 ($ x)) (open₀ t1' ($ x))) →
    para (abs T t1) (abs T t1')

inductive multi_red : Trm → Trm → Prop
| mr_refl : ∀ (t : Trm), lc t → multi_red t t
| mr_head : ∀ (t1 : Trm) (t2 : Trm) (t3 : Trm),
    multi_red t1 t2 → beta_red t2 t3 → multi_red t1 t3

inductive multi_para : Trm → Trm → Prop
| m_para_refl : ∀ (t : Trm), lc t → multi_para t t
| m_para_head : ∀ (t1 : Trm) (t2 : Trm) (t3 : Trm),
    multi_para t1 t2 → para t2 t3 → multi_para t1 t3

inductive typing : Env → Trm → Typ → Prop
| typ_var (Γ : Env) (x : Var) (T : Typ) :
    Env.valid_ctx Γ → Env.binds x T Γ → typing Γ ($ x) T
| typ_abs (L : Finset Var) (Γ : Env) (t : Trm) (T1 T2 : Typ) :
    ((x : Var) → x ∉ L → typing ((x, T1) :: Γ) (open₀ t ($ x)) T2) →
    typing Γ (abs T1 t) (Typ.typ_arrow T1 T2)
| typ_app (Γ : Env) (t₁ t₂ : Trm) (T1 T2 : Typ) :
    typing Γ t₁ (Typ.typ_arrow T1 T2) → typing Γ t₂ T1 → typing Γ (app t₁ t₂) T2

inductive value : Trm → Prop
| value_abs : ∀ (e : Trm) (T : Typ), lc (abs T e) → value (abs T e)

inductive eval : Trm → Trm → Prop
| eval_beta : ∀ (e1 : Trm) (e2 : Trm) (T : Typ),
    lc (abs T e1) → value e2 → eval (app (abs T e1) e2) (open₀ e1 e2)
| eval_app1 : ∀ (e1 : Trm) (e1' : Trm) (e2 : Trm),
    lc e2 → eval e1 e1' → eval (app e1 e2) (app e1' e2)
| eval_app2 : ∀ (e1 : Trm) (e2 : Trm) (e2' : Trm),
    lc e1 → eval e2 e2' → eval (app e1 e2) (app e1 e2')

end Lp2lc.Active.STLC
