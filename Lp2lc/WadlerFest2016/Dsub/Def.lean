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

-- Basic aliases
abbrev Vars := Finset Var

/- Environment as a list of (Var × Typ). In Dsub, variable bindings carry a type.
We reuse Shared.Env utilities for dom and mapping, and List.lookup for binds. -/
-- Forward decl: Typ is defined below; we use a mutual section to avoid issues.

/- Coq Dsub.v line 24: Inductive Typ/Trm (mutual) -/
mutual
  inductive Typ : Type where
    | typ_top   : Typ                              -- line 25
    | typ_sel   : Trm -> Typ                       -- line 26
    | typ_mem   : Bool -> Typ -> Typ               -- line 27  (bool indicates exact vs upper-bound)
    | typ_all   : Typ -> Typ -> Typ                -- line 28
  deriving Repr, BEq, DecidableEq

  inductive Trm : Type where
    | trm_bvar : Nat -> Trm                        -- line 33
    | trm_fvar : Var -> Trm                        -- line 34
    | trm_abs  : Typ -> Trm -> Trm                 -- line 35
    | trm_mem  : Typ -> Trm                        -- line 36
    | trm_app  : Trm -> Trm -> Trm                 -- line 37
  deriving Repr, BEq, DecidableEq
end

abbrev Env := List (Var × Typ)                    -- Coq line 109 (LibEnv.Env Typ)

/-- Domain of an environment - reuse Shared Env.domOf -/
def dom (E : Env) : Vars := Env.domOf E

/- Coq lines 39-56: open_t_rec and open_e_rec (mutual) -/
mutual
  def open_t_rec (k : Nat) (f : Trm) (T : Typ) : Typ :=
    match T with
    | Typ.typ_top       => Typ.typ_top
    | Typ.typ_sel t     => Typ.typ_sel (open_e_rec k f t)
    | Typ.typ_mem b T1  => Typ.typ_mem b (open_t_rec k f T1)
    | Typ.typ_all T1 T2 => Typ.typ_all (open_t_rec k f T1) (open_t_rec (k+1) f T2)

  def open_e_rec (k : Nat) (f : Trm) (e : Trm) : Trm :=
    match e with
    | Trm.trm_bvar i    => if k = i then f else Trm.trm_bvar i
    | Trm.trm_fvar x    => Trm.trm_fvar x
    | Trm.trm_abs V e1  => Trm.trm_abs (open_t_rec k f V) (open_e_rec (k+1) f e1)
    | Trm.trm_mem T     => Trm.trm_mem (open_t_rec k f T)
    | Trm.trm_app e1 e2 => Trm.trm_app (open_e_rec k f e1) (open_e_rec k f e2)
end

-- Coq lines 58-60: shorthands
def open_t (T : Typ) (f : Trm) : Typ := open_t_rec 0 f T
def open_e (t : Trm) (u : Trm) : Trm := open_e_rec 0 u t

-- Coq lines 63-65: notations
notation:67 T " open_t_var " x => open_t T (Trm.trm_fvar x)
notation:67 t " open_e_var " x => open_e t (Trm.trm_fvar x)

/- Coq lines 68-97: Local closure (types and terms) -/
mutual
  inductive DefType : Typ -> Prop where
    | type_top :
        DefType Typ.typ_top                                   -- line 70
    | type_sel : (e1 : Trm) ->
        DefTerm e1 ->
        DefType (Typ.typ_sel e1)                              -- lines 71-73
    | type_mem : (b : Bool) -> (T1 : Typ) ->
        DefType T1 ->
        DefType (Typ.typ_mem b T1)                            -- lines 74-76
    | type_all : (L : Vars) -> (T1 T2 : Typ) ->
        DefType T1 ->
        (∀ x, x ∉ L -> DefType (open_t T2 (Trm.trm_fvar x))) ->
        DefType (Typ.typ_all T1 T2)                           -- lines 77-81

  inductive DefTerm : Trm -> Prop where
    | term_var : (x : Var) ->
        DefTerm (Trm.trm_fvar x)                              -- lines 85-86
    | term_abs : (L : Vars) -> (V : Typ) -> (e1 : Trm) ->
        DefType V ->
        (∀ x, x ∉ L -> DefTerm (open_e e1 (Trm.trm_fvar x))) ->
        DefTerm (Trm.trm_abs V e1)                            -- lines 87-90
    | term_mem : (T1 : Typ) ->
        DefType T1 ->
        DefTerm (Trm.trm_mem T1)                              -- lines 91-93
    | term_app : (e1 e2 : Trm) ->
        DefTerm e1 -> DefTerm e2 ->
        DefTerm (Trm.trm_app e1 e2)                           -- lines 94-97
end

/-- Coq lines 101-106: Values -/
inductive Value : Trm -> Prop where
  | value_abs  : (V : Typ) -> (e1 : Trm) -> DefTerm (Trm.trm_abs V e1) ->
                 Value (Trm.trm_abs V e1)
  | value_mem : (V : Typ) -> DefTerm (Trm.trm_mem V) ->
                 Value (Trm.trm_mem V)

/- Coq lines 111-131: Well-formedness of types/terms in Env (mutual) -/
mutual
  inductive Wft : Env -> Typ -> Prop where
    | wft_top : (E : Env) ->
        Wft E Typ.typ_top                                       -- line 118
    | wft_sel : (E : Env) -> (e : Trm) ->
        (Value e ∨ ∃ x, Trm.trm_fvar x = e) ->
        Wfe E e ->
        Wft E (Typ.typ_sel e)                                   -- lines 119-123
    | wft_mem : (E : Env) -> (b : Bool) -> (T1 : Typ) ->
        Wft E T1 -> Wft E (Typ.typ_mem b T1)                    -- lines 123-125
    | wft_all : (L : Vars) -> (E : Env) -> (T1 T2 : Typ) ->
        Wft E T1 ->
        (∀ x, x ∉ L -> Wft ((x, T1) :: E) (open_t T2 (Trm.trm_fvar x))) ->
        Wft E (Typ.typ_all T1 T2)                               -- lines 126-130

  inductive Wfe : Env -> Trm -> Prop where
    | wfe_var : (U : Typ) -> (E : Env) -> (x : Var) ->
        (E.lookup x = some U) ->
        Wfe E (Trm.trm_fvar x)                                  -- lines 132-135
    | wfe_abs : (L : Vars) -> (E : Env) -> (V : Typ) -> (e : Trm) ->
        Wft E V ->
        (∀ x, x ∉ L -> Wfe ((x, V) :: E) (open_e e (Trm.trm_fvar x))) ->
        Wfe E (Trm.trm_abs V e)                                 -- lines 135-138
    | wfe_mem : (E : Env) -> (T : Typ) ->
        Wft E T -> Wfe E (Trm.trm_mem T)                        -- lines 139-141
    | wfe_app : (E : Env) -> (e1 e2 : Trm) ->
        Wfe E e1 -> Wfe E e2 ->
        Wfe E (Trm.trm_app e1 e2)                               -- lines 142-145
end

/-- Coq lines 152-156: Well-formed environments -/
-- alias for abstract ok predicate from Shared (used in some lemmas)
-- use shared ok from Lp2lc.Active.Shared

inductive Okt : Env -> Prop where
  | okt_empty : Okt []                                          -- lines 153-154
  | okt_push : (E : Env) -> (x : Var) -> (T : Typ) ->
      Okt E -> Wft E T -> (E.lookup x = none) -> Okt ((x, T) :: E) -- line 156

/- Coq lines 159-206: Sub / Has (mutual) -/
mutual
  inductive Sub : Env -> Typ -> Typ -> Prop where
    | sub_top : (E : Env) -> (S : Typ) ->
        Okt E -> Wft E S -> Sub E S Typ.typ_top                 -- lines 161-164
    | sub_refl_sel : (E : Env) -> (t : Trm) ->
        Okt E -> Wft E (Typ.typ_sel t) -> Sub E (Typ.typ_sel t) (Typ.typ_sel t)
        -- lines 165-168
    | sub_sel1 : (E : Env) -> (U : Typ) -> (t : Trm) ->
        Has E t (Typ.typ_mem false U) -> Sub E (Typ.typ_sel t) U -- lines 169-171
    | sub_sel2 : (E : Env) -> (S : Typ) -> (t : Trm) ->
        Has E t (Typ.typ_mem true S) -> Sub E S (Typ.typ_sel t)  -- lines 172-174
    | sub_mem_false : (E : Env) -> (b1 : Bool) -> (T1 T2 : Typ) ->
        Sub E T1 T2 -> Sub E (Typ.typ_mem b1 T1) (Typ.typ_mem false T2)
        -- lines 175-178
    | sub_mem_true : (E : Env) -> (T1 T2 : Typ) ->
        Sub E T1 T2 -> Sub E T2 T1 ->
        Sub E (Typ.typ_mem true T1) (Typ.typ_mem true T2)        -- lines 178-181
    | sub_all : (L : Vars) -> (E : Env) -> (S1 S2 T1 T2 : Typ) ->
        Sub E T1 S1 ->
        (∀ x, x ∉ L -> Sub ((x, T1) :: E) (open_t S2 (Trm.trm_fvar x)) (open_t T2 (Trm.trm_fvar x))) ->
        Sub E (Typ.typ_all S1 S2) (Typ.typ_all T1 T2)            -- lines 181-185
    | sub_trans : (E : Env) -> (S T U : Typ) ->
        Sub E S T -> Sub E T U -> Sub E S U                      -- lines 186-189

  inductive Has : Env -> Trm -> Typ -> Prop where
    | has_var : (E : Env) -> (x : Var) -> (T : Typ) ->
        Okt E -> (E.lookup x = some T) -> Has E (Trm.trm_fvar x) T -- 191-195
    | has_mem : (E : Env) -> (b : Bool) -> (T : Typ) ->
        Okt E -> Wft E T -> Has E (Trm.trm_mem T) (Typ.typ_mem b T) -- 196-198
    | has_abs : (E : Env) -> (V : Typ) -> (e : Trm) -> (T : Typ) ->
        Okt E -> Wfe E (Trm.trm_abs V e) -> Wft E (Typ.typ_all V T) ->
        Has E (Trm.trm_abs V e) (Typ.typ_all V T)                   -- 199-201
    | has_sub : (E : Env) -> (t : Trm) -> (T U : Typ) ->
        Has E t T -> Sub E T U -> Has E t U                         -- 202-205
end

/-- Coq lines 210-238: Typing -/
inductive Typing : Env -> Trm -> Typ -> Prop where
  | typing_var : (E : Env) -> (x : Var) -> (T : Typ) ->
      Okt E -> (E.lookup x = some T) -> Typing E (Trm.trm_fvar x) T -- 211-214
  | typing_abs : (L : Vars) -> (E : Env) -> (V : Typ) -> (e1 : Trm) -> (T1 : Typ) ->
      (∀ x, x ∉ L -> Typing ((x, V) :: E) (open_e e1 (Trm.trm_fvar x)) (open_t T1 (Trm.trm_fvar x))) ->
      Typing E (Trm.trm_abs V e1) (Typ.typ_all V T1)                -- 215-218
  | typing_mem : (E : Env) -> (T1 : Typ) ->
      Okt E -> Wft E T1 -> Typing E (Trm.trm_mem T1) (Typ.typ_mem true T1) -- 219-222
  | typing_app : (T1 : Typ) -> (E : Env) -> (e1 e2 : Trm) -> (T2 : Typ) ->
      Typing E e1 (Typ.typ_all T1 T2) -> Typing E e2 T1 -> Wft E T2 ->
      Typing E (Trm.trm_app e1 e2) T2                               -- 223-227
  | typing_appvar : (T1 : Typ) -> (E : Env) -> (e1 e2 : Trm) -> (T2 T2' : Typ) -> (M : Typ) ->
      Typing E e1 (Typ.typ_all T1 T2) -> Typing E e2 T1 -> Has E e2 M ->
      T2' = open_t T2 e2 -> Wft E T2' -> Typing E (Trm.trm_app e1 e2) T2' -- 228-234
  | typing_sub : (S : Typ) -> (E : Env) -> (e : Trm) -> (T : Typ) ->
      Typing E e S -> Sub E S T -> Typing E e T                      -- 235-238

/-- Coq lines 242-254: One-step reduction -/
inductive Red : Trm -> Trm -> Prop where
  | red_app_1 : (e1 e1' e2 : Trm) ->
      DefTerm e2 -> Red e1 e1' -> Red (Trm.trm_app e1 e2) (Trm.trm_app e1' e2)
  | red_app_2 : (e1 e2 e2' : Trm) ->
      Value e1 -> Red e2 e2' -> Red (Trm.trm_app e1 e2) (Trm.trm_app e1 e2')
  | red_abs : (V : Typ) -> (e1 : Trm) -> (v2 : Trm) ->
      DefTerm (Trm.trm_abs V e1) -> Value v2 ->
      Red (Trm.trm_app (Trm.trm_abs V e1) v2) (open_e e1 v2)

/-- Coq lines 258-266: Predicate statements for main theorems -/
def preservation : Prop := ∀ (e e' : Trm) (T : Typ),
  Typing [] e T -> Red e e' -> Typing [] e' T

def progress : Prop := ∀ (e : Trm) (T : Typ),
  Typing [] e T -> Value e ∨ ∃ e', Red e e'

/- Coq lines 1423-1451: Psub (pseudo-subtyping under empty Env) -/
inductive Psub : Typ -> Typ -> Prop where
  | psub_top : (S : Typ) ->
      Wft [] S -> Psub S Typ.typ_top
  | psub_refl_sel : (t : Trm) ->
      Wft [] (Typ.typ_sel t) -> Psub (Typ.typ_sel t) (Typ.typ_sel t)
  | psub_sel1 : (U : Typ) ->
      Wft [] U -> Psub (Typ.typ_sel (Trm.trm_mem U)) U
  | psub_sel2 : (S : Typ) ->
      Wft [] S -> Psub S (Typ.typ_sel (Trm.trm_mem S))
  | psub_mem_false : (b1 : Bool) -> (T1 T2 : Typ) ->
      Psub T1 T2 -> Psub (Typ.typ_mem b1 T1) (Typ.typ_mem false T2)
  | psub_mem_true : (T1 T2 : Typ) ->
      Psub T1 T2 -> Psub T2 T1 -> Psub (Typ.typ_mem true T1) (Typ.typ_mem true T2)
  | psub_all : (L : Vars) -> (S1 S2 T1 T2 : Typ) ->
      Psub T1 S1 ->
      (∀ x, x ∉ L ->
          Sub ((x, T1) :: []) (open_t S2 (Trm.trm_fvar x)) (open_t T2 (Trm.trm_fvar x))) ->
      Psub (Typ.typ_all S1 S2) (Typ.typ_all T1 T2)
  | psub_trans : (S T U : Typ) ->
      Psub S T -> Psub T U -> Psub S U

/- Coq lines 1478-1493: PossibleTypes -/
inductive PossibleTypes : Nat -> Trm -> Typ -> Prop where
  | pt_top : (n : Nat) -> (v : Trm) -> Value v -> Wfe [] v ->
      PossibleTypes n v Typ.typ_top
  | pt_mem_true : (n : Nat) -> (T T' : Typ) -> Psub T T' -> Psub T' T ->
      PossibleTypes n (Trm.trm_mem T) (Typ.typ_mem true T')
  | pt_mem_false : (n : Nat) -> (T U : Typ) -> Psub T U ->
      PossibleTypes n (Trm.trm_mem T) (Typ.typ_mem false U)
  | pt_all : (L : Vars) -> (n : Nat) -> (V V' : Typ) -> (e1 : Trm) -> (T1 T1' : Typ) ->
      (∀ X, X ∉ L -> Typing ((X, V) :: []) (open_e e1 (Trm.trm_fvar X)) (open_t T1 (Trm.trm_fvar X))) ->
      Psub V' V ->
      (∀ X, X ∉ L -> Sub ((X, V') :: []) (open_t T1 (Trm.trm_fvar X)) (open_t T1' (Trm.trm_fvar X))) ->
      PossibleTypes (Nat.succ n) (Trm.trm_abs V e1) (Typ.typ_all V' T1')
  | pt_all_shallow : (V V' : Typ) -> (e1 : Trm) -> (T1' : Typ) ->
      Wfe [] (Trm.trm_abs V e1) -> Wft [] (Typ.typ_all V' T1') ->
      PossibleTypes 0 (Trm.trm_abs V e1) (Typ.typ_all V' T1')
  | pt_sel : (n : Nat) -> (v : Trm) -> (S : Typ) -> PossibleTypes n v S ->
      PossibleTypes n v (Typ.typ_sel (Trm.trm_mem S))

/- Coq lines 275-294: Free variables (mutual) -/
mutual
  def fv_t (T : Typ) : Vars :=
    match T with
    | Typ.typ_top       => ∅
    | Typ.typ_sel t     => fv_e t
    | Typ.typ_mem _ T1  => fv_t T1
    | Typ.typ_all T1 T2 => (fv_t T1) ∪ (fv_t T2)

  def fv_e (e : Trm) : Vars :=
    match e with
    | Trm.trm_bvar _    => ∅
    | Trm.trm_fvar x    => {x}
    | Trm.trm_abs V e1  => (fv_t V) ∪ (fv_e e1)
    | Trm.trm_mem T     => fv_t T
    | Trm.trm_app e1 e2 => (fv_e e1) ∪ (fv_e e2)
end

/- Coq lines 298-315: Substitution (mutual) -/
mutual
  def subst_t (z : Var) (u : Trm) (T : Typ) : Typ :=
    match T with
    | Typ.typ_top       => Typ.typ_top
    | Typ.typ_sel t     => Typ.typ_sel (subst_e z u t)
    | Typ.typ_mem b T1  => Typ.typ_mem b (subst_t z u T1)
    | Typ.typ_all T1 T2 => Typ.typ_all (subst_t z u T1) (subst_t z u T2)

def subst_e (z : Var) (u : Trm) (e : Trm) : Trm :=
    match e with
    | Trm.trm_bvar i    => Trm.trm_bvar i
    | Trm.trm_fvar x    => by
        classical
        exact (if h : x = z then (by simpa [h] using u) else Trm.trm_fvar x)
    | Trm.trm_abs V e1  => Trm.trm_abs (subst_t z u V) (subst_e z u e1)
    | Trm.trm_mem T1    => Trm.trm_mem (subst_t z u T1)
    | Trm.trm_app e1 e2 => Trm.trm_app (subst_e z u e1) (subst_e z u e2)
end

/- Map a term-substitution on types across an environment -/
def map_subst_t (Z : Var) (u : Trm) (E : Env) : Env :=
  Env.mapSecond (λ T => subst_t Z u T) E

end Lp2lc.Active.Dsub
