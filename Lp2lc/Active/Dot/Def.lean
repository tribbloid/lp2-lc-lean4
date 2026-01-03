import Std
import Mathlib.Data.Finset.Basic

import Aesop
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Dot

-- Provide a local alias for shared environment well-formedness
-- use shared ok from Lp2lc.Active.Shared

-- [Coq: Dot.v line 13]
structure typ_label where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

-- [Coq: Dot.v line 14]
structure trm_label where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

-- Bring shared Var and Vars into scope
abbrev Var := Lp2lc.Active.Var
abbrev Vars := Lp2lc.Active.Vars

-- Simple env helpers specialized to this module
namespace Env
  def binds {α} (x : Var) (v : α) (E : List (Var × α)) : Prop :=
    E.lookup x = some v
  def dom {α} (E : List (Var × α)) : Vars := E.map (·.1) |>.toFinset
end Env

-- [Coq: Dot.v line 16]
inductive label : Type where
  | label_typ : typ_label → label
  | label_trm : trm_label → label
  deriving Repr, DecidableEq

-- [Coq: Dot.v line 20]
inductive avar : Type where
  | avar_b : Nat → avar -- bound var (de Bruijn index)
  | avar_f : Var → avar -- free var
  deriving Repr, DecidableEq

-- Forward mutual declarations
mutual
  -- [Coq: Dot.v line 24]
  inductive typ : Type where
    | typ_rcd : dec → typ
    | typ_and : typ → typ → typ
    | typ_sel : avar → typ_label → typ
    | typ_bnd : typ → typ
    | typ_all : typ → typ → typ
  deriving Repr, DecidableEq

  -- [Coq: Dot.v line 30]
  inductive dec : Type where
    | dec_typ : typ_label → typ → typ → dec
    | dec_trm : trm_label → typ → dec
  deriving Repr, DecidableEq

  -- [Coq: Dot.v line 34]
  inductive trm : Type where
    | trm_var : avar → trm
    | trm_val : val → trm
    | trm_sel : avar → trm_label → trm
    | trm_app : avar → avar → trm
    | trm_let : trm → trm → trm
  deriving Repr, DecidableEq

  -- [Coq: Dot.v line 40]
  inductive val : Type where
    | val_new : typ → defs → val
    | val_lambda : typ → trm → val
  deriving Repr, DecidableEq

  -- [Coq: Dot.v line 43]
  inductive defn : Type where
    | def_typ : typ_label → typ → defn
    | def_trm : trm_label → trm → defn
  deriving Repr, DecidableEq

  -- [Coq: Dot.v line 46]
  inductive defs : Type where
    | defs_nil : defs
    | defs_cons : defs → defn → defs
  deriving Repr, DecidableEq
end

-- Note: def is reserved in Lean; we use defn and document the rename.
-- Aliases for environments
-- [Coq: Dot.v line 51]
abbrev ctx := List (Var × typ)
-- [Coq: Dot.v line 54]
abbrev sto := List (Var × val)

-- [Coq: Dot.v line 59]
def label_of_def (d : defn) : label :=
  match d with
  | defn.def_typ L _ => label.label_typ L
  | defn.def_trm m _ => label.label_trm m

-- [Coq: Dot.v line 64]
def label_of_dec (D : dec) : label :=
  match D with
  | dec.dec_typ L _ _ => label.label_typ L
  | dec.dec_trm m _ => label.label_trm m

-- [Coq: Dot.v line 69]
partial def get_def (l : label) : defs → Option defn
  | defs.defs_nil => none
  | defs.defs_cons ds' d => if label_of_def d = l then some d else get_def l ds'

-- [Coq: Dot.v line 75]
def defs_has (ds : defs) (d : defn) : Prop := get_def (label_of_def d) ds = some d
-- [Coq: Dot.v line 76]
def defs_hasnt (ds : defs) (l : label) : Prop := get_def l ds = none

-- Opening operations
-- [Coq: Dot.v line 84]
def open_rec_avar (k : Nat) (u : Var) (a : avar) : avar :=
  match a with
  | avar.avar_b i => if k = i then avar.avar_f u else avar.avar_b i
  | avar.avar_f x => avar.avar_f x

-- Mutually recursive open operations
mutual
  -- [Coq: Dot.v line 90]
  partial def open_rec_typ (k : Nat) (u : Var) (T : typ) : typ :=
    match T with
    | typ.typ_rcd D      => typ.typ_rcd (open_rec_dec k u D)
    | typ.typ_and T1 T2  => typ.typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
    | typ.typ_sel x L    => typ.typ_sel (open_rec_avar k u x) L
    | typ.typ_bnd T      => typ.typ_bnd (open_rec_typ (k+1) u T)
    | typ.typ_all T1 T2  => typ.typ_all (open_rec_typ k u T1) (open_rec_typ (k+1) u T2)

  -- [Coq: Dot.v line 98]
  partial def open_rec_dec (k : Nat) (u : Var) (D : dec) : dec :=
    match D with
    | dec.dec_typ L T U => dec.dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
    | dec.dec_trm m T => dec.dec_trm m (open_rec_typ k u T)

  -- [Coq: Dot.v line 104]
  partial def open_rec_trm (k : Nat) (u : Var) (t : trm) : trm :=
    match t with
    | trm.trm_var a      => trm.trm_var (open_rec_avar k u a)
    | trm.trm_val v      => trm.trm_val (open_rec_val k u v)
    | trm.trm_sel v m    => trm.trm_sel (open_rec_avar k u v) m
    | trm.trm_app f a    => trm.trm_app (open_rec_avar k u f) (open_rec_avar k u a)
    | trm.trm_let t1 t2  => trm.trm_let (open_rec_trm k u t1) (open_rec_trm (k+1) u t2)

  -- [Coq: Dot.v line 112]
  partial def open_rec_val (k : Nat) (u : Var) (v : val) : val :=
    match v with
    | val.val_new T ds => val.val_new (open_rec_typ (k+1) u T) (open_rec_defs (k+1) u ds)
    | val.val_lambda T e => val.val_lambda (open_rec_typ k u T) (open_rec_trm (k+1) u e)

  -- [Coq: Dot.v line 117]
  partial def open_rec_def (k : Nat) (u : Var) (d : defn) : defn :=
    match d with
    | defn.def_typ L T => defn.def_typ L (open_rec_typ k u T)
    | defn.def_trm m e => defn.def_trm m (open_rec_trm k u e)

  -- [Coq: Dot.v line 122]
  partial def open_rec_defs (k : Nat) (u : Var) (ds : defs) : defs :=
    match ds with
    | defs.defs_nil => defs.defs_nil
    | defs.defs_cons tl d => defs.defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
end

-- [Coq: Dot.v line 128]
abbrev open_avar (u : Var) (a : avar) := open_rec_avar 0 u a
-- [Coq: Dot.v line 129]
abbrev open_typ  (u : Var) (t : typ) := open_rec_typ 0 u t
-- [Coq: Dot.v line 130]
abbrev open_dec  (u : Var) (D : dec) := open_rec_dec 0 u D
-- [Coq: Dot.v line 131]
abbrev open_trm  (u : Var) (e : trm) := open_rec_trm 0 u e
-- [Coq: Dot.v line 132]
abbrev open_val  (u : Var) (v : val) := open_rec_val 0 u v
-- [Coq: Dot.v line 133]
abbrev open_def  (u : Var) (d : defn) := open_rec_def 0 u d
-- [Coq: Dot.v line 134]
abbrev open_defs (u : Var) (l : defs) := open_rec_defs 0 u l

-- Substitution operations
-- [Coq: Dot.v lines 653-697]
namespace Subst
  -- [Coq: Dot.v line 761]
  def subst_fvar (x y z : Var) : Var := if z = x then y else z

  -- [Coq: Dot.v line 653]
  def subst_avar (z u : Var) (a : avar) : avar :=
    match a with
    | avar.avar_b i => avar.avar_b i
    | avar.avar_f x => avar.avar_f (if x = z then u else x)

  mutual
    -- [Coq: Dot.v lines 659-666]
    partial def subst_typ (z u : Var) (T : typ) : typ :=
      match T with
      | typ.typ_rcd D      => typ.typ_rcd (subst_dec z u D)
      | typ.typ_and T1 T2  => typ.typ_and (subst_typ z u T1) (subst_typ z u T2)
      | typ.typ_sel x L    => typ.typ_sel (subst_avar z u x) L
      | typ.typ_bnd T      => typ.typ_bnd (subst_typ z u T)
      | typ.typ_all T U    => typ.typ_all (subst_typ z u T) (subst_typ z u U)

    -- [Coq: Dot.v lines 667-671]
    partial def subst_dec (z u : Var) (D : dec) : dec :=
      match D with
      | dec.dec_typ L T U => dec.dec_typ L (subst_typ z u T) (subst_typ z u U)
      | dec.dec_trm L U   => dec.dec_trm L (subst_typ z u U)

    -- [Coq: Dot.v lines 673-680]
    partial def subst_trm (z u : Var) (t : trm) : trm :=
      match t with
      | trm.trm_var x        => trm.trm_var (subst_avar z u x)
      | trm.trm_val v        => trm.trm_val (subst_val z u v)
      | trm.trm_sel x1 L     => trm.trm_sel (subst_avar z u x1) L
      | trm.trm_app x1 x2    => trm.trm_app (subst_avar z u x1) (subst_avar z u x2)
      | trm.trm_let t1 t2    => trm.trm_let (subst_trm z u t1) (subst_trm z u t2)

    -- [Coq: Dot.v lines 681-695]
    partial def subst_val (z u : Var) (v : val) : val :=
      match v with
      | val.val_new T ds     => val.val_new (subst_typ z u T) (subst_defs z u ds)
      | val.val_lambda T t   => val.val_lambda (subst_typ z u T) (subst_trm z u t)

    -- [Coq: Dot.v lines 686-690]
    partial def subst_def (z u : Var) (d : defn) : defn :=
      match d with
      | defn.def_typ L T => defn.def_typ L (subst_typ z u T)
      | defn.def_trm L t => defn.def_trm L (subst_trm z u t)

    -- [Coq: Dot.v lines 691-695]
    partial def subst_defs (z u : Var) (ds : defs) : defs :=
      match ds with
      | defs.defs_nil        => defs.defs_nil
      | defs.defs_cons rest d => defs.defs_cons (subst_defs z u rest) (subst_def z u d)
  end

  -- [Coq: Dot.v line 697]
  def subst_ctx (z u : Var) (G : ctx) : ctx :=
    G.map (fun p => (p.1, subst_typ z u p.2))
end Subst

open Subst

-- Free variables (Vars is Finset Var)
-- [Coq: Dot.v line 139]
def fv_avar (a : avar) : Vars :=
  match a with
  | avar.avar_b _ => ∅
  | avar.avar_f x => {x}

-- Mutually recursive fv functions
mutual
  -- [Coq: Dot.v line 145]
  partial def fv_typ (T : typ) : Vars :=
    match T with
    | typ.typ_rcd D      => fv_dec D
    | typ.typ_and T U    => fv_typ T ∪ fv_typ U
    | typ.typ_sel x _    => fv_avar x
    | typ.typ_bnd T      => fv_typ T
    | typ.typ_all T1 T2  => fv_typ T1 ∪ fv_typ T2

  -- [Coq: Dot.v line 153]
  partial def fv_dec (D : dec) : Vars :=
    match D with
    | dec.dec_typ _ T U => fv_typ T ∪ fv_typ U
    | dec.dec_trm _ T   => fv_typ T

  -- [Coq: Dot.v line 159]
  partial def fv_trm (t : trm) : Vars :=
    match t with
    | trm.trm_var a       => fv_avar a
    | trm.trm_val v       => fv_val v
    | trm.trm_sel x _     => fv_avar x
    | trm.trm_app f a     => fv_avar f ∪ fv_avar a
    | trm.trm_let t1 t2   => fv_trm t1 ∪ fv_trm t2

  -- [Coq: Dot.v line 167]
  partial def fv_val (v : val) : Vars :=
    match v with
    | val.val_new T ds    => fv_typ T ∪ fv_defs ds
    | val.val_lambda T e  => fv_typ T ∪ fv_trm e

  -- [Coq: Dot.v line 172]
  partial def fv_def (d : defn) : Vars :=
    match d with
    | defn.def_typ _ T     => fv_typ T
    | defn.def_trm _ t     => fv_trm t

  -- [Coq: Dot.v line 177]
  partial def fv_defs (ds : defs) : Vars :=
    match ds with
    | defs.defs_nil         => ∅
    | defs.defs_cons tl d   => fv_defs tl ∪ fv_def d
end

-- [Coq: Dot.v line 183]
def fv_ctx_types (G : ctx) : Vars :=
  G.foldl (init := (∅ : Vars)) (fun acc (_, T) => acc ∪ fv_typ T)

-- Relations (inductives in Prop)

-- [Coq: Dot.v line 188]
inductive red : trm → sto → trm → sto → Prop where
  | red_sel : ∀ x m s t T ds,
      Env.binds x (val.val_new T ds) s →
      defs_has (open_defs x ds) (defn.def_trm m t) →
      red (trm.trm_sel (avar.avar_f x) m) s t s
  | red_app : ∀ f a s T t,
      Env.binds f (val.val_lambda T t) s →
      red (trm.trm_app (avar.avar_f f) (avar.avar_f a)) s (open_trm a t) s
  | red_let : ∀ v t s x,
      x ∉ Env.dom s →
      red (trm.trm_let (trm.trm_val v) t) s (open_trm x t) ((x, v) :: s)
  | red_let_var : ∀ t s x,
      red (trm.trm_let (trm.trm_var (avar.avar_f x)) t) s (open_trm x t) s
  | red_let_tgt : ∀ t0 t s t0' s',
      red t0 s t0' s' →
      red (trm.trm_let t0 t) s (trm.trm_let t0' t) s'

-- [Coq: Dot.v lines 208-314]
inductive tymode : Type := | ty_precise | ty_general
inductive submode : Type := | sub_tight | sub_general

mutual
  inductive ty_trm : tymode → submode → ctx → trm → typ → Prop where
    | ty_var : ∀ (m1 : tymode) (m2 : submode) (G : ctx) (x : Var) (T : typ),
        Env.binds x T G →
        ty_trm m1 m2 G (trm.trm_var (avar.avar_f x)) T
    | ty_all_intro : ∀ (L : Vars) (m1 : tymode) (m2 : submode) (G : ctx) (T : typ) (t : trm) (U : typ),
        (∀ (x : Var), x ∉ L →
          ty_trm ty_general sub_general ((x, T) :: G) (open_trm x t) (open_typ x U)) →
        ty_trm m1 m2 G (trm.trm_val (val.val_lambda T t)) (typ.typ_all T U)
    | ty_all_elim : ∀ (m2 : submode) (G : ctx) (x z : Var) (S T : typ),
        ty_trm ty_general m2 G (trm.trm_var (avar.avar_f x)) (typ.typ_all S T) →
        ty_trm ty_general m2 G (trm.trm_var (avar.avar_f z)) S →
        ty_trm ty_general m2 G (trm.trm_app (avar.avar_f x) (avar.avar_f z)) (open_typ z T)
    | ty_new_intro : ∀ (L : Vars) (m1 : tymode) (m2 : submode) (G : ctx) (T : typ) (ds : defs),
        (∀ (x : Var), x ∉ L →
          ty_defs ((x, open_typ x T) :: G) (open_defs x ds) (open_typ x T)) →
        ty_trm m1 m2 G (trm.trm_val (val.val_new T ds)) (typ.typ_bnd T)
    | ty_new_elim : ∀ (m2 : submode) (G : ctx) (x : Var) (m : trm_label) (T : typ),
        ty_trm ty_general m2 G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_trm m T)) →
        ty_trm ty_general m2 G (trm.trm_sel (avar.avar_f x) m) T
    | ty_let : ∀ (L : Vars) (m2 : submode) (G : ctx) (t u : trm) (T U : typ),
        ty_trm ty_general m2 G t T →
        (∀ (x : Var), x ∉ L →
          ty_trm ty_general sub_general ((x, T) :: G) (open_trm x u) U) →
        ty_trm ty_general m2 G (trm.trm_let t u) U
    | ty_rec_intro : ∀ (m2 : submode) (G : ctx) (x : Var) (T : typ),
        ty_trm ty_general m2 G (trm.trm_var (avar.avar_f x)) (open_typ x T) →
        ty_trm ty_general m2 G (trm.trm_var (avar.avar_f x)) (typ.typ_bnd T)
    | ty_rec_elim : ∀ (m1 : tymode) (m2 : submode) (G : ctx) (x : Var) (T : typ),
        ty_trm m1 m2 G (trm.trm_var (avar.avar_f x)) (typ.typ_bnd T) →
        ty_trm m1 m2 G (trm.trm_var (avar.avar_f x)) (open_typ x T)
    | ty_and_intro : ∀ (m2 : submode) (G : ctx) (x : Var) (T U : typ),
        ty_trm ty_general m2 G (trm.trm_var (avar.avar_f x)) T →
        ty_trm ty_general m2 G (trm.trm_var (avar.avar_f x)) U →
        ty_trm ty_general m2 G (trm.trm_var (avar.avar_f x)) (typ.typ_and T U)
    | ty_sub : ∀ (m1 : tymode) (m2 : submode) (G : ctx) (t : trm) (T U : typ),
        (m1 = ty_precise → ∃ x, t = trm.trm_var (avar.avar_f x)) →
        ty_trm m1 m2 G t T →
        subtyp ty_general m2 G T U →
        ty_trm m1 m2 G t U
  
  inductive ty_def : ctx → defn → dec → Prop where
    | ty_def_typ : ∀ (G : ctx) (A : typ_label) (T : typ),
        ty_def G (defn.def_typ A T) (dec.dec_typ A T T)
    | ty_def_trm : ∀ (G : ctx) (a : trm_label) (t : trm) (T : typ),
        ty_trm ty_general sub_general G t T →
        ty_def G (defn.def_trm a t) (dec.dec_trm a T)
  
  inductive ty_defs : ctx → defs → typ → Prop where
    | ty_defs_one : ∀ (G : ctx) (d : defn) (D : dec),
        ty_def G d D →
        ty_defs G (defs.defs_cons defs.defs_nil d) (typ.typ_rcd D)
    | ty_defs_cons : ∀ (G : ctx) (ds : defs) (d : defn) (T : typ) (D : dec),
        ty_defs G ds T →
        ty_def G d D →
        defs_hasnt ds (label_of_def d) →
        ty_defs G (defs.defs_cons ds d) (typ.typ_and T (typ.typ_rcd D))

  -- [Coq: Dot.v lines 266-305]
  inductive subtyp : tymode → submode → ctx → typ → typ → Prop where
    | subtyp_refl : ∀ (m2 : submode) (G : ctx) (T : typ),
        subtyp ty_general m2 G T T
    | subtyp_trans : ∀ (m1 : tymode) (m2 : submode) (G : ctx) (S T U : typ),
        subtyp m1 m2 G S T →
        subtyp m1 m2 G T U →
        subtyp m1 m2 G S U
    | subtyp_and11 : ∀ (m1 : tymode) (m2 : submode) (G : ctx) (T U : typ),
        subtyp m1 m2 G (typ.typ_and T U) T
    | subtyp_and12 : ∀ (m1 : tymode) (m2 : submode) (G : ctx) (T U : typ),
        subtyp m1 m2 G (typ.typ_and T U) U
    | subtyp_and2 : ∀ (m2 : submode) (G : ctx) (S T U : typ),
        subtyp ty_general m2 G S T →
        subtyp ty_general m2 G S U →
        subtyp ty_general m2 G S (typ.typ_and T U)
    | subtyp_fld : ∀ (m2 : submode) (G : ctx) (a : trm_label) (T U : typ),
        subtyp ty_general m2 G T U →
        subtyp ty_general m2 G (typ.typ_rcd (dec.dec_trm a T)) (typ.typ_rcd (dec.dec_trm a U))
    | subtyp_typ : ∀ (m2 : submode) (G : ctx) (A : typ_label) (S1 T1 S2 T2 : typ),
        subtyp ty_general m2 G S2 S1 →
        subtyp ty_general m2 G T1 T2 →
        subtyp ty_general m2 G (typ.typ_rcd (dec.dec_typ A S1 T1)) (typ.typ_rcd (dec.dec_typ A S2 T2))
    | subtyp_sel2 : ∀ (G : ctx) (x : Var) (A : typ_label) (S T : typ),
        ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_typ A S T)) →
        subtyp ty_general sub_general G S (typ.typ_sel (avar.avar_f x) A)
    | subtyp_sel1 : ∀ (G : ctx) (x : Var) (A : typ_label) (S T : typ),
        ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_typ A S T)) →
        subtyp ty_general sub_general G (typ.typ_sel (avar.avar_f x) A) T
    | subtyp_sel2_tight : ∀ (G : ctx) (x : Var) (A : typ_label) (T : typ),
        ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_typ A T T)) →
        subtyp ty_general sub_tight G T (typ.typ_sel (avar.avar_f x) A)
    | subtyp_sel1_tight : ∀ (G : ctx) (x : Var) (A : typ_label) (T : typ),
        ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_typ A T T)) →
        subtyp ty_general sub_tight G (typ.typ_sel (avar.avar_f x) A) T
    | subtyp_all : ∀ (L : Vars) (m2 : submode) (G : ctx) (S1 T1 S2 T2 : typ),
        subtyp ty_general m2 G S2 S1 →
        (∀ (x : Var), x ∉ L → subtyp ty_general sub_general ((x, S2) :: G) (open_typ x T1) (open_typ x T2)) →
        subtyp ty_general m2 G (typ.typ_all S1 T1) (typ.typ_all S2 T2)
end

-- moved into mutual block above

-- [Coq: Dot.v lines 306-314]
inductive wf_sto : ctx → sto → Prop where
  | wf_sto_empty : wf_sto [] []
  | wf_sto_push : ∀ (G : ctx) (s : sto) (x : Var) (T : typ) (v : val),
      wf_sto G s → x ∉ Env.dom G → x ∉ Env.dom s →
      ty_trm ty_precise sub_general G (trm.trm_val v) T →
      wf_sto ((x, T) :: G) ((x, v) :: s)

-- Record machinery
-- [Coq: Dot.v lines 1300-1316]
inductive record_dec : dec → Prop where
  | rd_typ : ∀ A T, record_dec (dec.dec_typ A T T)
  | rd_trm : ∀ a T, record_dec (dec.dec_trm a T)

-- [Coq: Dot.v lines 1305-1316]
inductive record_typ : typ → Finset label → Prop where
  | rt_one : ∀ D l,
      record_dec D → l = label_of_dec D → record_typ (typ.typ_rcd D) {l}
  | rt_cons : ∀ T ls D l,
      record_typ T ls → record_dec D → l = label_of_dec D → l ∉ ls →
      record_typ (typ.typ_and T (typ.typ_rcd D)) (ls ∪ {l})

-- [Coq: Dot.v line 1318]
def record_type (T : typ) : Prop := ∃ ls, record_typ T ls

-- [Coq: Dot.v lines 1542-1554]
inductive record_sub : typ → typ → Prop where
  | rs_refl : ∀ T, record_sub T T
  | rs_dropl : ∀ T T' D, record_sub T T' → record_sub (typ.typ_and T (typ.typ_rcd D)) (typ.typ_rcd D)
  | rs_drop  : ∀ T T' D, record_sub T T' → record_sub (typ.typ_and T (typ.typ_rcd D)) T'
  | rs_pick  : ∀ T T' D, record_sub T T' → record_sub (typ.typ_and T (typ.typ_rcd D)) (typ.typ_and T' (typ.typ_rcd D))

-- Has-member family
-- [Coq: Dot.v lines 1960-1981]
mutual
  inductive has_member : ctx → Var → typ → typ_label → typ → typ → Prop where
    | has_any : ∀ (G : ctx) (x : Var) (T : typ) (A : typ_label) (S U : typ),
        ty_trm ty_general sub_tight G (trm.trm_var (avar.avar_f x)) T →
        has_member_rules G x T A S U →
        has_member G x T A S U
  
  inductive has_member_rules : ctx → Var → typ → typ_label → typ → typ → Prop where
    | has_refl : ∀ (G : ctx) (x : Var) (A : typ_label) (S U : typ),
        has_member_rules G x (typ.typ_rcd (dec.dec_typ A S U)) A S U
    | has_and1 : ∀ (G : ctx) (x : Var) (T1 T2 : typ) (A : typ_label) (S U : typ),
        has_member G x T1 A S U → has_member_rules G x (typ.typ_and T1 T2) A S U
    | has_and2 : ∀ (G : ctx) (x : Var) (T1 T2 : typ) (A : typ_label) (S U : typ),
        has_member G x T2 A S U → has_member_rules G x (typ.typ_and T1 T2) A S U
    | has_bnd : ∀ (G : ctx) (x : Var) (T : typ) (A : typ_label) (S U : typ),
        has_member G x (open_typ x T) A S U → has_member_rules G x (typ.typ_bnd T) A S U
    | has_sel : ∀ (G : ctx) (x y : Var) (B : typ_label) (T' : typ) (A : typ_label) (S U : typ),
        ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f y)) (typ.typ_rcd (dec.dec_typ B T' T')) →
        has_member G x T' A S U →
        has_member_rules G x (typ.typ_sel (avar.avar_f y) B) A S U
end

-- Possible types (suffix of Dot.v)
-- [Coq: Dot.v lines 2365-2396]
inductive possible_types : ctx → Var → val → typ → Prop where
  | pt_new : ∀ (G : ctx) (x : Var) (T : typ) (ds : defs),
      possible_types G x (val.val_new T ds) (open_typ x T)
  | pt_rcd_trm : ∀ (G : ctx) (x : Var) (T : typ) (ds : defs) (a : trm_label) (t : trm) (T' : typ),
      defs_has (open_defs x ds) (defn.def_trm a t) →
      ty_trm ty_general sub_general G t T' →
      possible_types G x (val.val_new T ds) (typ.typ_rcd (dec.dec_trm a T'))
  | pt_rcd_typ : ∀ (G : ctx) (x : Var) (T : typ) (ds : defs) (A : typ_label) (T' S U : typ),
      defs_has (open_defs x ds) (defn.def_typ A T') →
      subtyp ty_general sub_general G S T' →
      subtyp ty_general sub_general G T' U →
      possible_types G x (val.val_new T ds) (typ.typ_rcd (dec.dec_typ A S U))
  | pt_lambda : ∀ (L : Vars) (G : ctx) (x : Var) (S : typ) (t : trm) (T S' T' : typ),
      (∀ (y : Var), y ∉ L → ty_trm ty_general sub_general ((y, S) :: G) (open_trm y t) (open_typ y T)) →
      subtyp ty_general sub_general G S' S →
      (∀ (y : Var), y ∉ L → subtyp ty_general sub_general ((y, S') :: G) (open_typ y T) (open_typ y T')) →
      possible_types G x (val.val_lambda S t) (typ.typ_all S' T')
  | pt_and : ∀ (G : ctx) (x : Var) (v : val) (S1 S2 : typ),
      possible_types G x v S1 → possible_types G x v S2 → possible_types G x v (typ.typ_and S1 S2)
  | pt_sel : ∀ (G : ctx) (x : Var) (v : val) (y : avar) (A : typ_label) (S : typ),
      possible_types G x v S → ty_trm ty_precise sub_general G (trm.trm_var y) (typ.typ_rcd (dec.dec_typ A S S)) →
      possible_types G x v (typ.typ_sel y A)
  | pt_bnd : ∀ (G : ctx) (x : Var) (v : val) (S S' : typ),
      possible_types G x v S → S = open_typ x S' → possible_types G x v (typ.typ_bnd S')

-- [Coq: Dot.v lines 2461-2469]
inductive record_has : typ → dec → Prop where
  | rh_one : ∀ D, record_has (typ.typ_rcd D) D
  | rh_andl : ∀ T D, record_has (typ.typ_and T (typ.typ_rcd D)) D
  | rh_and : ∀ T D D', record_has T D' → record_has (typ.typ_and T D) D'

-- [Coq: Dot.v lines 3044-3047]
inductive normal_form : trm → Prop where
  | nf_var : ∀ (x : avar), normal_form (trm.trm_var x)
  | nf_val : ∀ (v : val), normal_form (trm.trm_val v)

end Lp2lc.Active.Dot
