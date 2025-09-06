-- Line 1: Preservation and Progress for System-F with Subtyping, Bottom and Lower Bounds
-- Line 15: Import TLC.LibTactics -> Lean 4 equivalents
import Std
import Mathlib.Data.Finset.Basic
import Aesop

namespace Lp2lc.Active.FsubL_alt

-- Basic variable and finite sets of variables
structure Var where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

abbrev Vars := Finset Var

-- Line 30: Representation of pre-types (extended with bottom)
inductive Typ : Type where
  | typ_top : Typ
  | typ_bot : Typ  -- Line 32: Added bottom type
  | typ_bvar : Nat → Typ
  | typ_fvar : Var → Typ
  | typ_arrow : Typ → Typ → Typ
  | typ_all : Typ → Typ → Typ → Typ  -- Line 36: Extended with lower bound
  deriving Repr

-- Line 40: Representation of pre-terms (extended with bounds in type abstraction)
inductive Trm : Type where
  | trm_bvar : Nat → Trm
  | trm_fvar : Var → Trm
  | trm_abs : Typ → Trm → Trm
  | trm_app : Trm → Trm → Trm
  | trm_tabs : Typ → Typ → Trm → Trm  -- Line 45: Extended with lower and upper bounds
  | trm_tapp : Trm → Typ → Trm
  deriving Repr

-- Line 140: Binding are either mapping type or term variables (extended with bounds)
inductive Bind : Type where
  | bind_sub : Typ → Typ → Bind  -- Line 141: Extended with lower and upper bounds
  | bind_typ : Typ → Bind
  deriving Repr

-- Concrete environment implementation (association list of (Var × Bind))
structure Env where
  entries : List (Var × Bind) := []
  deriving Repr

namespace Env

instance : EmptyCollection Env where
  emptyCollection := { entries := [] }

def push (E : Env) (p : Var × Bind) : Env := { entries := p :: E.entries }

def dom (E : Env) : Vars :=
  E.entries.foldl (init := (∅ : Vars)) fun acc (vk, _) => {vk} ∪ acc

end Env

-- Binding lookup in environments
def binds (x : Var) (b : Bind) (E : Env) : Prop := (x, b) ∈ E.entries

-- Line 50: Opening up a type binder occuring in a type
def open_tt_rec (K : Nat) (U : Typ) (T : Typ) : Typ :=
  match T with
  | Typ.typ_top => Typ.typ_top
  | Typ.typ_bot => Typ.typ_bot  -- Line 53: Handle bottom type
  | Typ.typ_bvar J => if K = J then U else Typ.typ_bvar J
  | Typ.typ_fvar X => Typ.typ_fvar X
  | Typ.typ_arrow T1 T2 => Typ.typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | Typ.typ_all T0 T1 T2 => Typ.typ_all (open_tt_rec K U T0) (open_tt_rec K U T1) (open_tt_rec (K + 1) U T2)
    -- Line 57: Handle three type arguments with bounds

-- Line 60: Definition open_tt T U := open_tt_rec 0 U T
def open_tt (T U : Typ) : Typ := open_tt_rec 0 U T

-- Line 64: Opening up a type binder occuring in a term
def open_te_rec (K : Nat) (U : Typ) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i => Trm.trm_bvar i
  | Trm.trm_fvar x => Trm.trm_fvar x
  | Trm.trm_abs V e1 => Trm.trm_abs (open_tt_rec K U V) (open_te_rec K U e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (open_te_rec K U e1) (open_te_rec K U e2)
  | Trm.trm_tabs VS VU e1 => Trm.trm_tabs (open_tt_rec K U VS) (open_tt_rec K U VU) (open_te_rec (K + 1) U e1)
    -- Line 70: Handle bounded type abstraction with lower and upper bounds
  | Trm.trm_tapp e1 V => Trm.trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)

-- Line 74: Definition open_te t U := open_te_rec 0 U t
def open_te (t : Trm) (U : Typ) : Trm := open_te_rec 0 U t

-- Line 78: Opening up a term binder occuring in a term
def open_ee_rec (k : Nat) (f : Trm) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i => if k = i then f else Trm.trm_bvar i
  | Trm.trm_fvar x => Trm.trm_fvar x
  | Trm.trm_abs V e1 => Trm.trm_abs V (open_ee_rec (k + 1) f e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | Trm.trm_tabs VS VU e1 => Trm.trm_tabs VS VU (open_ee_rec k f e1)  -- Line 84: Preserve bounds
  | Trm.trm_tapp e1 V => Trm.trm_tapp (open_ee_rec k f e1) V

-- Line 88: Definition open_ee t u := open_ee_rec 0 u t
def open_ee (t u : Trm) : Trm := open_ee_rec 0 u t

-- Line 92: Notation for opening up binders with type or term variables
notation:67 T " open_tt_var " X => open_tt T (Typ.typ_fvar X)
notation:67 t " open_te_var " X => open_te t (Typ.typ_fvar X)
notation:67 t " open_ee_var " x => open_ee t (Trm.trm_fvar x)

-- Line 98: Types as locally closed pre-types (extended with bottom)
inductive type : Typ → Prop where
  | type_top : type Typ.typ_top
  | type_bot : type Typ.typ_bot  -- Line 101: Bottom type is well-formed
  | type_var : ∀ (X : Var), type (Typ.typ_fvar X)
  | type_arrow : ∀ (T1 T2 : Typ), type T1 → type T2 → type (Typ.typ_arrow T1 T2)
  | type_all : ∀ (L : Vars) (T0 T1 T2 : Typ), type T0 → type T1 → 
    (∀ (X : Var), X ∉ L → type (T2 open_tt_var X)) → type (Typ.typ_all T0 T1 T2)
    -- Line 109: Extended with lower bound T0 and upper bound T1

-- Line 117: Terms as locally closed pre-terms (extended with bounded type abstraction)
inductive term : Trm → Prop where
  | term_var : ∀ (x : Var), term (Trm.trm_fvar x)
  | term_abs : ∀ (L : Vars) (V : Typ) (e1 : Trm), type V →
    (∀ (x : Var), x ∉ L → term (e1 open_ee_var x)) → term (Trm.trm_abs V e1)
  | term_app : ∀ (e1 e2 : Trm), term e1 → term e2 → term (Trm.trm_app e1 e2)
  | term_tabs : ∀ (L : Vars) (VS VU : Typ) (e1 : Trm), type VS → type VU →
    (∀ (X : Var), X ∉ L → term (e1 open_te_var X)) → term (Trm.trm_tabs VS VU e1)
    -- Line 128: Extended with lower bound VS and upper bound VU
  | term_tapp : ∀ (e1 : Trm) (V : Typ), term e1 → type V → term (Trm.trm_tapp e1 V)

-- Bind already defined above to avoid circular dependencies

-- Line 146: Environment is an associative list of bindings (already defined above)
-- def Env := LibEnv.env Bind

-- Line 153: Well-formedness of a pre-type T in an environment E (extended)
inductive wft : Env → Typ → Prop where
  | wft_top : ∀ (E : Env), wft E Typ.typ_top
  | wft_bot : ∀ (E : Env), wft E Typ.typ_bot  -- Line 156: Bottom type is well-formed
  | wft_var : ∀ (T0 T1 : Typ) (E : Env) (X : Var), binds X (Bind.bind_sub T0 T1) E → wft E (Typ.typ_fvar X)
    -- Line 158: Type variable requires bounded binding
  | wft_arrow : ∀ (E : Env) (T1 T2 : Typ), wft E T1 → wft E T2 → wft E (Typ.typ_arrow T1 T2)
  | wft_all : ∀ (L : Vars) (E : Env) (T0 T1 T2 : Typ), wft E T0 → wft E T1 →
    (∀ (X : Var), X ∉ L → wft (Env.push E (X, Bind.bind_sub T0 T1)) (T2 open_tt_var X)) → 
    wft E (Typ.typ_all T0 T1 T2)
    -- Line 165: Extended with bounds T0 and T1

-- Line 176: A environment E is well-formed (extended with bounds)
inductive okt : Env → Prop where
  | okt_empty : okt (∅ : Env)
  | okt_sub : ∀ (E : Env) (X : Var) (T0 T1 : Typ), okt E → wft E T0 → wft E T1 → X ∉ Env.dom E → 
    okt (Env.push E (X, Bind.bind_sub T0 T1))  -- Line 179: Extended with bounds
  | okt_typ : ∀ (E : Env) (x : Var) (T : Typ), okt E → wft E T → x ∉ Env.dom E → okt (Env.push E (x, Bind.bind_typ T))

-- Line 186: Subtyping relation (extended with bottom, bounds, and transitivity)
inductive sub : Env → Typ → Typ → Prop where
  | sub_top : ∀ (E : Env) (S : Typ), okt E → wft E S → sub E S Typ.typ_top
  | sub_bot : ∀ (E : Env) (T : Typ), okt E → wft E T → sub E Typ.typ_bot T  -- Line 191: Bottom is subtype of all
  | sub_refl_tvar : ∀ (E : Env) (X : Var), okt E → wft E (Typ.typ_fvar X) → 
    sub E (Typ.typ_fvar X) (Typ.typ_fvar X)
  | sub_tvar : ∀ (T0 T1 : Typ) (E : Env) (X : Var), okt E → binds X (Bind.bind_sub T0 T1) E → 
    sub E (Typ.typ_fvar X) T1  -- Line 199: Use upper bound
  | sub_tvar_lower : ∀ (T0 T1 : Typ) (E : Env) (X : Var), okt E → binds X (Bind.bind_sub T0 T1) E → 
    sub E T0 (Typ.typ_fvar X)  -- Line 203: Use lower bound
  | sub_arrow : ∀ (E : Env) (S1 S2 T1 T2 : Typ), sub E T1 S1 → sub E S2 T2 → 
    sub E (Typ.typ_arrow S1 S2) (Typ.typ_arrow T1 T2)
  | sub_all : ∀ (L : Vars) (E : Env) (S0 S1 S2 T0 T1 T2 : Typ), sub E S0 T0 → sub E T1 S1 →
    (∀ (X : Var), X ∉ L → sub (Env.push E (X, Bind.bind_sub T0 T1)) (S2 open_tt_var X) (T2 open_tt_var X)) →
    sub E (Typ.typ_all S0 S1 S2) (Typ.typ_all T0 T1 T2)
    -- Line 211: Extended with bounds handling
  | sub_trans : ∀ (E : Env) (S T U : Typ), sub E S T → sub E T U → sub E S U  -- Line 217: Explicit transitivity

-- Line 225: Typing relation (extended with bounded type abstraction)
inductive typing : Env → Trm → Typ → Prop where
  | typing_var : ∀ (E : Env) (x : Var) (T : Typ), okt E → binds x (Bind.bind_typ T) E → typing E (Trm.trm_fvar x) T
  | typing_abs : ∀ (L : Vars) (E : Env) (V : Typ) (e1 : Trm) (T1 : Typ),
    (∀ (x : Var), x ∉ L → typing (Env.push E (x, Bind.bind_typ V)) (e1 open_ee_var x) T1) →
    typing E (Trm.trm_abs V e1) (Typ.typ_arrow V T1)
  | typing_app : ∀ (T1 : Typ) (E : Env) (e1 e2 : Trm) (T2 : Typ), typing E e1 (Typ.typ_arrow T1 T2) → typing E e2 T1 →
    typing E (Trm.trm_app e1 e2) T2
  | typing_tabs : ∀ (L : Vars) (E : Env) (VS VU : Typ) (e1 : Trm) (T1 : Typ),
    (∀ (X : Var), X ∉ L → typing (Env.push E (X, Bind.bind_sub VS VU)) (e1 open_te_var X) (T1 open_tt_var X)) →
    typing E (Trm.trm_tabs VS VU e1) (Typ.typ_all VS VU T1)
    -- Line 238: Extended with bounded type abstraction
  | typing_tapp : ∀ (T0 T1 : Typ) (E : Env) (e1 : Trm) (T : Typ) (T2 : Typ), typing E e1 (Typ.typ_all T0 T1 T2) → 
    sub E T0 T → sub E T T1 → typing E (Trm.trm_tapp e1 T) (open_tt T2 T)
    -- Line 242: Extended with bound checking
  | typing_sub : ∀ (S : Typ) (E : Env) (e : Trm) (T : Typ), typing E e S → sub E S T → typing E e T

-- Line 254: Values (extended with bounded type abstraction)
inductive value : Trm → Prop where
  | value_abs : ∀ (V : Typ) (e1 : Trm), term (Trm.trm_abs V e1) → value (Trm.trm_abs V e1)
  | value_tabs : ∀ (VS VU : Typ) (e1 : Trm), term (Trm.trm_tabs VS VU e1) → value (Trm.trm_tabs VS VU e1)
    -- Line 257: Extended with bounds

-- Line 262: One-step reduction (extended with bounded type abstraction)
inductive red : Trm → Trm → Prop where
  | red_app_1 : ∀ (e1 e1' e2 : Trm), term e2 → red e1 e1' → red (Trm.trm_app e1 e2) (Trm.trm_app e1' e2)
  | red_app_2 : ∀ (e1 e2 e2' : Trm), value e1 → red e2 e2' → red (Trm.trm_app e1 e2) (Trm.trm_app e1 e2')
  | red_tapp : ∀ (e1 e1' : Trm) (V : Typ), type V → red e1 e1' → red (Trm.trm_tapp e1 V) (Trm.trm_tapp e1' V)
  | red_abs : ∀ (V : Typ) (e1 v2 : Trm), term (Trm.trm_abs V e1) → value v2 →
    red (Trm.trm_app (Trm.trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : ∀ (V0 V1 : Typ) (e1 : Trm) (V2 : Typ), term (Trm.trm_tabs V0 V1 e1) → type V2 →
    red (Trm.trm_tapp (Trm.trm_tabs V0 V1 e1) V2) (open_te e1 V2)
    -- Line 279: Extended with bounds V0 V1

-- Line 286: Our goal is to prove preservation and progress
def preservation : Prop := ∀ (e e' : Trm) (T : Typ), typing (∅ : Env) e T → red e e' → typing (∅ : Env) e' T

def progress : Prop := ∀ (e : Trm) (T : Typ), typing (∅ : Env) e T → value e ∨ ∃ e', red e e'

-- Line 305: Computing free type variables in a type (extended)
def fv_tt : Typ → Set Var
  | Typ.typ_top => ∅
  | Typ.typ_bot => ∅  -- Line 308: Bottom has no free variables
  | Typ.typ_bvar _ => ∅
  | Typ.typ_fvar X => {X}
  | Typ.typ_arrow T1 T2 => fv_tt T1 ∪ fv_tt T2
  | Typ.typ_all T0 T1 T2 => fv_tt T0 ∪ fv_tt T1 ∪ fv_tt T2  -- Line 312: Extended with bounds

-- Line 317: Computing free type variables in a term (extended)
def fv_te : Trm → Set Var
  | Trm.trm_bvar _ => ∅
  | Trm.trm_fvar _ => ∅
  | Trm.trm_abs V e1 => fv_tt V ∪ fv_te e1
  | Trm.trm_app e1 e2 => fv_te e1 ∪ fv_te e2
  | Trm.trm_tabs VS VU e1 => fv_tt VS ∪ fv_tt VU ∪ fv_te e1  -- Line 323: Extended with bounds
  | Trm.trm_tapp e1 V => fv_tt V ∪ fv_te e1

-- Line 329: Computing free term variables in a term
def fv_ee : Trm → Set Var
  | Trm.trm_bvar _ => ∅
  | Trm.trm_fvar x => {x}
  | Trm.trm_abs _ e1 => fv_ee e1
  | Trm.trm_app e1 e2 => fv_ee e1 ∪ fv_ee e2
  | Trm.trm_tabs _ _ e1 => fv_ee e1  -- Line 335: Bounds don't affect term variables
  | Trm.trm_tapp e1 _ => fv_ee e1

-- Line 341: Substitution for free type variables in types (extended)
def subst_tt (Z : Var) (U : Typ) : Typ → Typ
  | Typ.typ_top => Typ.typ_top
  | Typ.typ_bot => Typ.typ_bot  -- Line 344: Bottom unchanged
  | Typ.typ_bvar J => Typ.typ_bvar J
  | Typ.typ_fvar X => if X = Z then U else Typ.typ_fvar X
  | Typ.typ_arrow T1 T2 => Typ.typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | Typ.typ_all T0 T1 T2 => Typ.typ_all (subst_tt Z U T0) (subst_tt Z U T1) (subst_tt Z U T2)
    -- Line 348: Extended with bounds

-- Line 353: Substitution for free type variables in terms (extended)
def subst_te (Z : Var) (U : Typ) : Trm → Trm
  | Trm.trm_bvar i => Trm.trm_bvar i
  | Trm.trm_fvar x => Trm.trm_fvar x
  | Trm.trm_abs V e1 => Trm.trm_abs (subst_tt Z U V) (subst_te Z U e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (subst_te Z U e1) (subst_te Z U e2)
  | Trm.trm_tabs VS VU e1 => Trm.trm_tabs (subst_tt Z U VS) (subst_tt Z U VU) (subst_te Z U e1)
    -- Line 359: Extended with bounds substitution
  | Trm.trm_tapp e1 V => Trm.trm_tapp (subst_te Z U e1) (subst_tt Z U V)

-- Line 365: Substitution for free term variables in terms
def subst_ee (z : Var) (u : Trm) : Trm → Trm
  | Trm.trm_bvar i => Trm.trm_bvar i
  | Trm.trm_fvar x => if x = z then u else Trm.trm_fvar x
  | Trm.trm_abs V e1 => Trm.trm_abs V (subst_ee z u e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (subst_ee z u e1) (subst_ee z u e2)
  | Trm.trm_tabs VS VU e1 => Trm.trm_tabs VS VU (subst_ee z u e1)  -- Line 371: Preserve bounds
  | Trm.trm_tapp e1 V => Trm.trm_tapp (subst_ee z u e1) V

-- Line 377: Substitution for free type variables in environment (extended)
def subst_tb (Z : Var) (P : Typ) : Bind → Bind
  | Bind.bind_sub T0 T1 => Bind.bind_sub (subst_tt Z P T0) (subst_tt Z P T1)  -- Line 379: Both bounds
  | Bind.bind_typ T => Bind.bind_typ (subst_tt Z P T)

end Lp2lc.Active.FsubL_alt
