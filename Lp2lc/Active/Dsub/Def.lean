/- Dsub (D<:)
T ::= Top | p.Type | { Type = T } | { Type <: T } | (z: T) -> T^z
 t ::= p | t t
 p ::= x | v
 v ::= { Type = T } | lambda x:T.t

Coq source: Lp2lc_coq/Active/Dsub.v
- This file ports definitions and inductives only (no axioms, no proofs).
- Every ported declaration is preceded by a comment with the original Coq line number.
- Followed conventions in .agents/CodeStructure.md and agents/ConversionRules.md.
-/

import Std
import Mathlib.Data.Finset.Basic

import Aesop
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Dsub

open Lp2lc.Active

-- Basic aliases
abbrev Vars := Finset Var

/- Environment as a list of (Var × typ). In Dsub, variable bindings carry a type.
We reuse Shared.Env utilities for dom and mapping, and List.lookup for binds. -/
-- Forward decl: typ is defined below; we use a mutual section to avoid issues.

/- Coq Dsub.v line 24: Inductive typ/trm (mutual) -/
mutual
  inductive typ : Type where
    | typ_top   : typ                              -- line 25
    | typ_sel   : trm -> typ                       -- line 26
    | typ_mem   : Bool -> typ -> typ               -- line 27  (bool indicates exact vs upper-bound)
    | typ_all   : typ -> typ -> typ                -- line 28
  deriving Repr, BEq, DecidableEq

  inductive trm : Type where
    | trm_bvar : Nat -> trm                        -- line 33
    | trm_fvar : Var -> trm                        -- line 34
    | trm_abs  : typ -> trm -> trm                 -- line 35
    | trm_mem  : typ -> trm                        -- line 36
    | trm_app  : trm -> trm -> trm                 -- line 37
  deriving Repr, BEq, DecidableEq
end

abbrev env := List (Var × typ)                    -- Coq line 109 (LibEnv.env typ)

/-- Domain of an environment - reuse Shared Env.domOf -/
def dom (E : env) : Vars := Env.domOf E

/- Coq lines 39-56: open_t_rec and open_e_rec (mutual) -/
mutual
  def open_t_rec (k : Nat) (f : trm) (T : typ) : typ :=
    match T with
    | typ.typ_top       => typ.typ_top
    | typ.typ_sel t     => typ.typ_sel (open_e_rec k f t)
    | typ.typ_mem b T1  => typ.typ_mem b (open_t_rec k f T1)
    | typ.typ_all T1 T2 => typ.typ_all (open_t_rec k f T1) (open_t_rec (k+1) f T2)

  def open_e_rec (k : Nat) (f : trm) (e : trm) : trm :=
    match e with
    | trm.trm_bvar i    => if k = i then f else trm.trm_bvar i
    | trm.trm_fvar x    => trm.trm_fvar x
    | trm.trm_abs V e1  => trm.trm_abs (open_t_rec k f V) (open_e_rec (k+1) f e1)
    | trm.trm_mem T     => trm.trm_mem (open_t_rec k f T)
    | trm.trm_app e1 e2 => trm.trm_app (open_e_rec k f e1) (open_e_rec k f e2)
end

-- Coq lines 58-60: shorthands
def open_t (T : typ) (f : trm) : typ := open_t_rec 0 f T
def open_e (t : trm) (u : trm) : trm := open_e_rec 0 u t

-- Coq lines 63-65: notations
notation:67 T " open_t_var " x => open_t T (trm.trm_fvar x)
notation:67 t " open_e_var " x => open_e t (trm.trm_fvar x)

/- Coq lines 68-97: Local closure (types and terms) -/
mutual
  inductive def_type : typ -> Prop where
    | type_top :
        def_type typ.typ_top                                   -- line 70
    | type_sel : (e1 : trm) ->
        def_term e1 ->
        def_type (typ.typ_sel e1)                              -- lines 71-73
    | type_mem : (b : Bool) -> (T1 : typ) ->
        def_type T1 ->
        def_type (typ.typ_mem b T1)                            -- lines 74-76
    | type_all : (L : Vars) -> (T1 T2 : typ) ->
        def_type T1 ->
        (∀ x, x ∉ L -> def_type (open_t T2 (trm.trm_fvar x))) ->
        def_type (typ.typ_all T1 T2)                           -- lines 77-81

  inductive def_term : trm -> Prop where
    | term_var : (x : Var) ->
        def_term (trm.trm_fvar x)                              -- lines 85-86
    | term_abs : (L : Vars) -> (V : typ) -> (e1 : trm) ->
        def_type V ->
        (∀ x, x ∉ L -> def_term (open_e e1 (trm.trm_fvar x))) ->
        def_term (trm.trm_abs V e1)                            -- lines 87-90
    | term_mem : (T1 : typ) ->
        def_type T1 ->
        def_term (trm.trm_mem T1)                              -- lines 91-93
    | term_app : (e1 e2 : trm) ->
        def_term e1 -> def_term e2 ->
        def_term (trm.trm_app e1 e2)                           -- lines 94-97
end

/-- Coq lines 101-106: Values -/
inductive value : trm -> Prop where
  | value_abs  : (V : typ) -> (e1 : trm) -> def_term (trm.trm_abs V e1) ->
                 value (trm.trm_abs V e1)
  | value_mem : (V : typ) -> def_term (trm.trm_mem V) ->
                 value (trm.trm_mem V)

/- Coq lines 111-131: Well-formedness of types/terms in env (mutual) -/
mutual
  inductive wft : env -> typ -> Prop where
    | wft_top : (E : env) ->
        wft E typ.typ_top                                       -- line 118
    | wft_sel : (E : env) -> (e : trm) ->
        (value e ∨ ∃ x, trm.trm_fvar x = e) ->
        wfe E e ->
        wft E (typ.typ_sel e)                                   -- lines 119-123
    | wft_mem : (E : env) -> (b : Bool) -> (T1 : typ) ->
        wft E T1 -> wft E (typ.typ_mem b T1)                    -- lines 123-125
    | wft_all : (L : Vars) -> (E : env) -> (T1 T2 : typ) ->
        wft E T1 ->
        (∀ x, x ∉ L -> wft ((x, T1) :: E) (open_t T2 (trm.trm_fvar x))) ->
        wft E (typ.typ_all T1 T2)                               -- lines 126-130

  inductive wfe : env -> trm -> Prop where
    | wfe_var : (U : typ) -> (E : env) -> (x : Var) ->
        (E.lookup x = some U) ->
        wfe E (trm.trm_fvar x)                                  -- lines 132-135
    | wfe_abs : (L : Vars) -> (E : env) -> (V : typ) -> (e : trm) ->
        wft E V ->
        (∀ x, x ∉ L -> wfe ((x, V) :: E) (open_e e (trm.trm_fvar x))) ->
        wfe E (trm.trm_abs V e)                                 -- lines 135-138
    | wfe_mem : (E : env) -> (T : typ) ->
        wft E T -> wfe E (trm.trm_mem T)                        -- lines 139-141
    | wfe_app : (E : env) -> (e1 e2 : trm) ->
        wfe E e1 -> wfe E e2 ->
        wfe E (trm.trm_app e1 e2)                               -- lines 142-145
end

/-- Coq lines 152-156: Well-formed environments -/
-- alias for abstract ok predicate from Shared (used in some lemmas)
-- use shared ok from Lp2lc.Active.Shared

inductive okt : env -> Prop where
  | okt_empty : okt []                                          -- lines 153-154
  | okt_push : (E : env) -> (x : Var) -> (T : typ) ->
      okt E -> wft E T -> (E.lookup x = none) -> okt ((x, T) :: E) -- line 156

/- Coq lines 159-206: sub / has (mutual) -/
mutual
  inductive sub : env -> typ -> typ -> Prop where
    | sub_top : (E : env) -> (S : typ) ->
        okt E -> wft E S -> sub E S typ.typ_top                 -- lines 161-164
    | sub_refl_sel : (E : env) -> (t : trm) ->
        okt E -> wft E (typ.typ_sel t) -> sub E (typ.typ_sel t) (typ.typ_sel t)
        -- lines 165-168
    | sub_sel1 : (E : env) -> (U : typ) -> (t : trm) ->
        has E t (typ.typ_mem false U) -> sub E (typ.typ_sel t) U -- lines 169-171
    | sub_sel2 : (E : env) -> (S : typ) -> (t : trm) ->
        has E t (typ.typ_mem true S) -> sub E S (typ.typ_sel t)  -- lines 172-174
    | sub_mem_false : (E : env) -> (b1 : Bool) -> (T1 T2 : typ) ->
        sub E T1 T2 -> sub E (typ.typ_mem b1 T1) (typ.typ_mem false T2)
        -- lines 175-178
    | sub_mem_true : (E : env) -> (T1 T2 : typ) ->
        sub E T1 T2 -> sub E T2 T1 ->
        sub E (typ.typ_mem true T1) (typ.typ_mem true T2)        -- lines 178-181
    | sub_all : (L : Vars) -> (E : env) -> (S1 S2 T1 T2 : typ) ->
        sub E T1 S1 ->
        (∀ x, x ∉ L -> sub ((x, T1) :: E) (open_t S2 (trm.trm_fvar x)) (open_t T2 (trm.trm_fvar x))) ->
        sub E (typ.typ_all S1 S2) (typ.typ_all T1 T2)            -- lines 181-185
    | sub_trans : (E : env) -> (S T U : typ) ->
        sub E S T -> sub E T U -> sub E S U                      -- lines 186-189

  inductive has : env -> trm -> typ -> Prop where
    | has_var : (E : env) -> (x : Var) -> (T : typ) ->
        okt E -> (E.lookup x = some T) -> has E (trm.trm_fvar x) T -- 191-195
    | has_mem : (E : env) -> (b : Bool) -> (T : typ) ->
        okt E -> wft E T -> has E (trm.trm_mem T) (typ.typ_mem b T) -- 196-198
    | has_abs : (E : env) -> (V : typ) -> (e : trm) -> (T : typ) ->
        okt E -> wfe E (trm.trm_abs V e) -> wft E (typ.typ_all V T) ->
        has E (trm.trm_abs V e) (typ.typ_all V T)                   -- 199-201
    | has_sub : (E : env) -> (t : trm) -> (T U : typ) ->
        has E t T -> sub E T U -> has E t U                         -- 202-205
end

/-- Coq lines 210-238: typing -/
inductive typing : env -> trm -> typ -> Prop where
  | typing_var : (E : env) -> (x : Var) -> (T : typ) ->
      okt E -> (E.lookup x = some T) -> typing E (trm.trm_fvar x) T -- 211-214
  | typing_abs : (L : Vars) -> (E : env) -> (V : typ) -> (e1 : trm) -> (T1 : typ) ->
      (∀ x, x ∉ L -> typing ((x, V) :: E) (open_e e1 (trm.trm_fvar x)) (open_t T1 (trm.trm_fvar x))) ->
      typing E (trm.trm_abs V e1) (typ.typ_all V T1)                -- 215-218
  | typing_mem : (E : env) -> (T1 : typ) ->
      okt E -> wft E T1 -> typing E (trm.trm_mem T1) (typ.typ_mem true T1) -- 219-222
  | typing_app : (T1 : typ) -> (E : env) -> (e1 e2 : trm) -> (T2 : typ) ->
      typing E e1 (typ.typ_all T1 T2) -> typing E e2 T1 -> wft E T2 ->
      typing E (trm.trm_app e1 e2) T2                               -- 223-227
  | typing_appvar : (T1 : typ) -> (E : env) -> (e1 e2 : trm) -> (T2 T2' : typ) -> (M : typ) ->
      typing E e1 (typ.typ_all T1 T2) -> typing E e2 T1 -> has E e2 M ->
      T2' = open_t T2 e2 -> wft E T2' -> typing E (trm.trm_app e1 e2) T2' -- 228-234
  | typing_sub : (S : typ) -> (E : env) -> (e : trm) -> (T : typ) ->
      typing E e S -> sub E S T -> typing E e T                      -- 235-238

/-- Coq lines 242-254: One-step reduction -/
inductive red : trm -> trm -> Prop where
  | red_app_1 : (e1 e1' e2 : trm) ->
      def_term e2 -> red e1 e1' -> red (trm.trm_app e1 e2) (trm.trm_app e1' e2)
  | red_app_2 : (e1 e2 e2' : trm) ->
      value e1 -> red e2 e2' -> red (trm.trm_app e1 e2) (trm.trm_app e1 e2')
  | red_abs : (V : typ) -> (e1 : trm) -> (v2 : trm) ->
      def_term (trm.trm_abs V e1) -> value v2 ->
      red (trm.trm_app (trm.trm_abs V e1) v2) (open_e e1 v2)

/-- Coq lines 258-266: Predicate statements for main theorems -/
def preservation : Prop := ∀ (e e' : trm) (T : typ),
  typing [] e T -> red e e' -> typing [] e' T

def progress : Prop := ∀ (e : trm) (T : typ),
  typing [] e T -> value e ∨ ∃ e', red e e'

/- Coq lines 1423-1451: psub (pseudo-subtyping under empty env) -/
inductive psub : typ -> typ -> Prop where
  | psub_top : (S : typ) ->
      wft [] S -> psub S typ.typ_top
  | psub_refl_sel : (t : trm) ->
      wft [] (typ.typ_sel t) -> psub (typ.typ_sel t) (typ.typ_sel t)
  | psub_sel1 : (U : typ) ->
      wft [] U -> psub (typ.typ_sel (trm.trm_mem U)) U
  | psub_sel2 : (S : typ) ->
      wft [] S -> psub S (typ.typ_sel (trm.trm_mem S))
  | psub_mem_false : (b1 : Bool) -> (T1 T2 : typ) ->
      psub T1 T2 -> psub (typ.typ_mem b1 T1) (typ.typ_mem false T2)
  | psub_mem_true : (T1 T2 : typ) ->
      psub T1 T2 -> psub T2 T1 -> psub (typ.typ_mem true T1) (typ.typ_mem true T2)
  | psub_all : (L : Vars) -> (S1 S2 T1 T2 : typ) ->
      psub T1 S1 ->
      (∀ x, x ∉ L ->
          sub ((x, T1) :: []) (open_t S2 (trm.trm_fvar x)) (open_t T2 (trm.trm_fvar x))) ->
      psub (typ.typ_all S1 S2) (typ.typ_all T1 T2)
  | psub_trans : (S T U : typ) ->
      psub S T -> psub T U -> psub S U

/- Coq lines 1478-1493: possible_types -/
inductive possible_types : Nat -> trm -> typ -> Prop where
  | pt_top : (n : Nat) -> (v : trm) -> value v -> wfe [] v ->
      possible_types n v typ.typ_top
  | pt_mem_true : (n : Nat) -> (T T' : typ) -> psub T T' -> psub T' T ->
      possible_types n (trm.trm_mem T) (typ.typ_mem true T')
  | pt_mem_false : (n : Nat) -> (T U : typ) -> psub T U ->
      possible_types n (trm.trm_mem T) (typ.typ_mem false U)
  | pt_all : (L : Vars) -> (n : Nat) -> (V V' : typ) -> (e1 : trm) -> (T1 T1' : typ) ->
      (∀ X, X ∉ L -> typing ((X, V) :: []) (open_e e1 (trm.trm_fvar X)) (open_t T1 (trm.trm_fvar X))) ->
      psub V' V ->
      (∀ X, X ∉ L -> sub ((X, V') :: []) (open_t T1 (trm.trm_fvar X)) (open_t T1' (trm.trm_fvar X))) ->
      possible_types (Nat.succ n) (trm.trm_abs V e1) (typ.typ_all V' T1')
  | pt_all_shallow : (V V' : typ) -> (e1 : trm) -> (T1' : typ) ->
      wfe [] (trm.trm_abs V e1) -> wft [] (typ.typ_all V' T1') ->
      possible_types 0 (trm.trm_abs V e1) (typ.typ_all V' T1')
  | pt_sel : (n : Nat) -> (v : trm) -> (S : typ) -> possible_types n v S ->
      possible_types n v (typ.typ_sel (trm.trm_mem S))

/- Coq lines 275-294: Free variables (mutual) -/
mutual
  def fv_t (T : typ) : Vars :=
    match T with
    | typ.typ_top       => ∅
    | typ.typ_sel t     => fv_e t
    | typ.typ_mem _ T1  => fv_t T1
    | typ.typ_all T1 T2 => (fv_t T1) ∪ (fv_t T2)

  def fv_e (e : trm) : Vars :=
    match e with
    | trm.trm_bvar _    => ∅
    | trm.trm_fvar x    => {x}
    | trm.trm_abs V e1  => (fv_t V) ∪ (fv_e e1)
    | trm.trm_mem T     => fv_t T
    | trm.trm_app e1 e2 => (fv_e e1) ∪ (fv_e e2)
end

/- Coq lines 298-315: Substitution (mutual) -/
mutual
  def subst_t (z : Var) (u : trm) (T : typ) : typ :=
    match T with
    | typ.typ_top       => typ.typ_top
    | typ.typ_sel t     => typ.typ_sel (subst_e z u t)
    | typ.typ_mem b T1  => typ.typ_mem b (subst_t z u T1)
    | typ.typ_all T1 T2 => typ.typ_all (subst_t z u T1) (subst_t z u T2)

def subst_e (z : Var) (u : trm) (e : trm) : trm :=
    match e with
    | trm.trm_bvar i    => trm.trm_bvar i
    | trm.trm_fvar x    => by
        classical
        exact (if h : x = z then (by simpa [h] using u) else trm.trm_fvar x)
    | trm.trm_abs V e1  => trm.trm_abs (subst_t z u V) (subst_e z u e1)
    | trm.trm_mem T1    => trm.trm_mem (subst_t z u T1)
    | trm.trm_app e1 e2 => trm.trm_app (subst_e z u e1) (subst_e z u e2)
end

/- Map a term-substitution on types across an environment -/
def map_subst_t (Z : Var) (u : trm) (E : env) : env :=
  Env.mapSecond (fun T => subst_t Z u T) E

end Lp2lc.Active.Dsub
