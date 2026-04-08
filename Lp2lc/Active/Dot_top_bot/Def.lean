import Std
import Mathlib.Data.Finset.Basic

import Aesop
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Dot_top_bot

-- Provide a local alias for shared environment well-formedness
-- use shared ok from Lp2lc.Active.Shared

-- [Coq: Dot_top_bot.v line 13]
structure TypLabel where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

-- [Coq: Dot_top_bot.v line 14]
structure TrmLabel where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

-- Bring shared Var and Vars into scope
abbrev Var := Lp2lc.Active.Var
abbrev Vars := Lp2lc.Active.Vars

-- Simple Env helpers specialized to this module
namespace Env
  def binds {α} (x : Var) (v : α) (E : List (Var × α)) : Prop :=
    E.lookup x = some v
  def dom {α} (E : List (Var × α)) : Vars := E.map (·.1) |>.toFinset
end Env

-- [Coq: Dot_top_bot.v line 16]
inductive Label : Type where
  | label_typ : TypLabel → Label
  | label_trm : TrmLabel → Label
  deriving Repr, DecidableEq

-- [Coq: Dot_top_bot.v line 20]
inductive Avar : Type where
  | avar_b : Nat → Avar -- bound var (de Bruijn serial)
  | avar_f : Var → Avar -- free var
  deriving Repr, DecidableEq

-- Forward mutual declarations
mutual
  -- [Coq: Dot_top_bot.v lines 24-32]
  inductive Typ : Type where
    -- Top/Any
    | typ_top  : Typ
    -- Bottom/Nothing
    | typ_bot  : Typ
    -- Record Piece, Intersecting it build a structural type, intersecting with a tag build a trait
    | typ_rcd  : Dec → Typ
    -- Intersection/Subtype TODO: need Union type
    | typ_and  : (left: Typ) → (right: Typ) → Typ
    -- Dependent selection of type member with a type label
    | typ_sel  : (var: Avar) → (label: TypLabel) → Typ
    -- Self binding / `this.type` in Scala
    -- the only way to use the above `typ_sel` with a de Bruijn serial is within a typ_bnd
    | typ_bnd  : (self: Typ) → Typ
    -- Dependent function (AKA forAll quantifier)
    -- tOut can be a dependent selection, e.g. {x: I => x.DepT}
    -- the typ_all in System F/FSub is half-assed, should rename them
    | typ_all  : (tIn: Typ) → (tOut: Typ) → Typ
  deriving Repr, DecidableEq

  -- [Coq: Dot_top_bot.v line 33]
  inductive Dec : Type where -- member declaration
    | dec_typ : TypLabel → (upperBound: Typ) → (lowerBound: Typ) → Dec
    | dec_trm : TrmLabel → Typ → Dec
  deriving Repr, DecidableEq

  -- [Coq: Dot_top_bot.v line 36]
  inductive Trm : Type where
    -- Free/Bounded Variable
    | trm_var : Avar → Trm
    -- Literal?
    | trm_val : Val → Trm
    -- selection of term member with a term label
    | trm_sel : Avar → TrmLabel → Trm
    -- function application
    | trm_app : Avar → Avar → Trm
    -- ??
    | trm_let : Trm → Trm → Trm
  deriving Repr, DecidableEq

  -- [Coq: Dot_top_bot.v line 42]
  inductive Val : Type where
    | val_new : Typ → Defs → Val
    | val_lambda : Typ → Trm → Val
  deriving Repr, DecidableEq

  -- [Coq: Dot_top_bot.v line 46]
  inductive Defn : Type where
    | def_typ : TypLabel → Typ → Defn
    | def_trm : TrmLabel → Trm → Defn
  deriving Repr, DecidableEq

  -- [Coq: Dot_top_bot.v line 49]
  inductive Defs : Type where
    | defs_nil : Defs
    | defs_cons : Defs → Defn → Defs
  deriving Repr, DecidableEq
end

-- Note: def is reserved in Lean; we use Defn and document the rename.
-- Aliases for environments
-- [Coq: Dot_top_bot.v line 53]
abbrev Ctx := List (Var × Typ)
-- [Coq: Dot_top_bot.v line 56]
abbrev Sto := List (Var × Val)

-- [Coq: Dot_top_bot.v lines 61-69]
def label_of_def (d : Defn) : Label :=
  match d with
  | Defn.def_typ L _ => Label.label_typ L
  | Defn.def_trm m _ => Label.label_trm m

-- [Coq: Dot_top_bot.v lines 66-69]
def label_of_dec (D : Dec) : Label :=
  match D with
  | Dec.dec_typ L _ _ => Label.label_typ L
  | Dec.dec_trm m _ => Label.label_trm m

-- [Coq: Dot_top_bot.v lines 71-79]
partial def get_def (l : Label) : Defs → Option Defn
  | Defs.defs_nil => none
  | Defs.defs_cons ds' d => if label_of_def d = l then some d else get_def l ds'

-- [Coq: Dot_top_bot.v lines 77-79]
def defs_has (ds : Defs) (d : Defn) : Prop := get_def (label_of_def d) ds = some d
-- [Coq: Dot_top_bot.v line 78]
def defs_hasnt (ds : Defs) (l : Label) : Prop := get_def l ds = none

-- ######################################################################
-- Opening

-- [Coq: Dot_top_bot.v line 86]
def open_rec_avar (k : Nat) (u : Var) (a : Avar) : Avar :=
  match a with
  | Avar.avar_b i => if k = i then Avar.avar_f u else Avar.avar_b i
  | Avar.avar_f x => Avar.avar_f x

-- Mutually recursive open operations
mutual
  -- [Coq: Dot_top_bot.v lines 92-101]
  partial def open_rec_typ (k : Nat) (u : Var) (T : Typ) : Typ :=
    match T with
    | Typ.typ_top       => Typ.typ_top
    | Typ.typ_bot       => Typ.typ_bot
    | Typ.typ_rcd D     => Typ.typ_rcd (open_rec_dec k u D)
    | Typ.typ_and T1 T2 => Typ.typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
    | Typ.typ_sel x L   => Typ.typ_sel (open_rec_avar k u x) L
    | Typ.typ_bnd T     => Typ.typ_bnd (open_rec_typ (k+1) u T)
    | Typ.typ_all T1 T2 => Typ.typ_all (open_rec_typ k u T1) (open_rec_typ (k+1) u T2)

  -- [Coq: Dot_top_bot.v lines 102-106]
  partial def open_rec_dec (k : Nat) (u : Var) (D : Dec) : Dec :=
    match D with
    | Dec.dec_typ L T U => Dec.dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
    | Dec.dec_trm m T => Dec.dec_trm m (open_rec_typ k u T)

  -- [Coq: Dot_top_bot.v lines 108-116]
  partial def open_rec_trm (k : Nat) (u : Var) (t : Trm) : Trm :=
    match t with
    | Trm.trm_var a      => Trm.trm_var (open_rec_avar k u a)
    | Trm.trm_val v      => Trm.trm_val (open_rec_val k u v)
    | Trm.trm_sel v m    => Trm.trm_sel (open_rec_avar k u v) m
    | Trm.trm_app f a    => Trm.trm_app (open_rec_avar k u f) (open_rec_avar k u a)
    | Trm.trm_let t1 t2  => Trm.trm_let (open_rec_trm k u t1) (open_rec_trm (k+1) u t2)

  -- [Coq: Dot_top_bot.v lines 117-120]
  partial def open_rec_val (k : Nat) (u : Var) (v : Val) : Val :=
    match v with
    | Val.val_new T ds => Val.val_new (open_rec_typ (k+1) u T) (open_rec_defs (k+1) u ds)
    | Val.val_lambda T e => Val.val_lambda (open_rec_typ k u T) (open_rec_trm (k+1) u e)

  -- [Coq: Dot_top_bot.v lines 121-125]
  partial def open_rec_def (k : Nat) (u : Var) (d : Defn) : Defn :=
    match d with
    | Defn.def_typ L T => Defn.def_typ L (open_rec_typ k u T)
    | Defn.def_trm m e => Defn.def_trm m (open_rec_trm k u e)

  -- [Coq: Dot_top_bot.v lines 126-130]
  partial def open_rec_defs (k : Nat) (u : Var) (ds : Defs) : Defs :=
    match ds with
    | Defs.defs_nil => Defs.defs_nil
    | Defs.defs_cons tl d => Defs.defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
end

-- [Coq: Dot_top_bot.v lines 132-139]
abbrev open_avar (u : Var) (a : Avar) := open_rec_avar 0 u a
abbrev open_typ  (u : Var) (t : Typ) := open_rec_typ 0 u t
abbrev open_dec  (u : Var) (D : Dec) := open_rec_dec 0 u D
abbrev open_trm  (u : Var) (e : Trm) := open_rec_trm 0 u e
abbrev open_val  (u : Var) (v : Val) := open_rec_val 0 u v
abbrev open_def  (u : Var) (d : Defn) := open_rec_def 0 u d
abbrev open_defs (u : Var) (l : Defs) := open_rec_defs 0 u l

-- ######################################################################
-- Free variables

-- [Coq: Dot_top_bot.v lines 143-147]
def fv_avar (a : Avar) : Vars :=
  match a with
  | Avar.avar_b _ => ∅
  | Avar.avar_f x => {x}

-- Mutually recursive fv functions
mutual
  -- [Coq: Dot_top_bot.v lines 149-158]
  partial def fv_typ (T : Typ) : Vars :=
    match T with
    | Typ.typ_top        => ∅
    | Typ.typ_bot        => ∅
    | Typ.typ_rcd D      => fv_dec D
    | Typ.typ_and T U    => fv_typ T ∪ fv_typ U
    | Typ.typ_sel x _    => fv_avar x
    | Typ.typ_bnd T      => fv_typ T
    | Typ.typ_all T1 T2  => fv_typ T1 ∪ fv_typ T2

  -- [Coq: Dot_top_bot.v lines 159-163]
  partial def fv_dec (D : Dec) : Vars :=
    match D with
    | Dec.dec_typ _ T U => fv_typ T ∪ fv_typ U
    | Dec.dec_trm _ T   => fv_typ T

  -- [Coq: Dot_top_bot.v lines 165-172]
  partial def fv_trm (t : Trm) : Vars :=
    match t with
    | Trm.trm_var a       => fv_avar a
    | Trm.trm_val v       => fv_val v
    | Trm.trm_sel x _     => fv_avar x
    | Trm.trm_app f a     => fv_avar f ∪ fv_avar a
    | Trm.trm_let t1 t2   => fv_trm t1 ∪ fv_trm t2

  -- [Coq: Dot_top_bot.v lines 173-177]
  partial def fv_val (v : Val) : Vars :=
    match v with
    | Val.val_new T ds    => fv_typ T ∪ fv_defs ds
    | Val.val_lambda T e  => fv_typ T ∪ fv_trm e

  -- [Coq: Dot_top_bot.v lines 178-187]
  partial def fv_def (d : Defn) : Vars :=
    match d with
    | Defn.def_typ _ T     => fv_typ T
    | Defn.def_trm _ t     => fv_trm t

  partial def fv_defs (ds : Defs) : Vars :=
    match ds with
    | Defs.defs_nil         => ∅
    | Defs.defs_cons tl d   => fv_defs tl ∪ fv_def d
end

-- [Coq: Dot_top_bot.v line 189]
def fv_ctx_types (G : Ctx) : Vars :=
  G.foldl (init := (∅ : Vars)) (fun acc (_, T) => acc ∪ fv_typ T)

-- ######################################################################
-- Substitution

-- [Coq: Dot_top_bot.v lines 663-710]
def subst_avar (z : Var) (u : Var) (a : Avar) : Avar :=
  match a with
  | Avar.avar_b i => Avar.avar_b i
  | Avar.avar_f x => Avar.avar_f (if x = z then u else x)

mutual
  -- [Coq: Dot_top_bot.v lines 669-678]
  partial def subst_typ (z : Var) (u : Var) (T : Typ) : Typ :=
    match T with
    | Typ.typ_top       => Typ.typ_top
    | Typ.typ_bot       => Typ.typ_bot
    | Typ.typ_rcd D     => Typ.typ_rcd (subst_dec z u D)
    | Typ.typ_and T1 T2 => Typ.typ_and (subst_typ z u T1) (subst_typ z u T2)
    | Typ.typ_sel x L   => Typ.typ_sel (subst_avar z u x) L
    | Typ.typ_bnd T     => Typ.typ_bnd (subst_typ z u T)
    | Typ.typ_all T U   => Typ.typ_all (subst_typ z u T) (subst_typ z u U)

  -- [Coq: Dot_top_bot.v lines 679-683]
  partial def subst_dec (z : Var) (u : Var) (D : Dec) : Dec :=
    match D with
    | Dec.dec_typ L T U => Dec.dec_typ L (subst_typ z u T) (subst_typ z u U)
    | Dec.dec_trm L U   => Dec.dec_trm L (subst_typ z u U)

  -- [Coq: Dot_top_bot.v lines 685-692]
  partial def subst_trm (z : Var) (u : Var) (t : Trm) : Trm :=
    match t with
    | Trm.trm_var x       => Trm.trm_var (subst_avar z u x)
    | Trm.trm_val v       => Trm.trm_val (subst_val z u v)
    | Trm.trm_sel x1 L    => Trm.trm_sel (subst_avar z u x1) L
    | Trm.trm_app x1 x2   => Trm.trm_app (subst_avar z u x1) (subst_avar z u x2)
    | Trm.trm_let t1 t2   => Trm.trm_let (subst_trm z u t1) (subst_trm z u t2)

  -- [Coq: Dot_top_bot.v lines 693-697]
  partial def subst_val (z : Var) (u : Var) (v : Val) : Val :=
    match v with
    | Val.val_new T ds    => Val.val_new (subst_typ z u T) (subst_defs z u ds)
    | Val.val_lambda T t  => Val.val_lambda (subst_typ z u T) (subst_trm z u t)

  -- [Coq: Dot_top_bot.v lines 698-702]
  partial def subst_def (z : Var) (u : Var) (d : Defn) : Defn :=
    match d with
    | Defn.def_typ L T => Defn.def_typ L (subst_typ z u T)
    | Defn.def_trm L t => Defn.def_trm L (subst_trm z u t)

  -- [Coq: Dot_top_bot.v lines 703-707]
  partial def subst_defs (z : Var) (u : Var) (ds : Defs) : Defs :=
    match ds with
    | Defs.defs_nil          => Defs.defs_nil
    | Defs.defs_cons rest d  => Defs.defs_cons (subst_defs z u rest) (subst_def z u d)
end

-- [Coq: Dot_top_bot.v line 709]
def subst_ctx (z : Var) (u : Var) (G : Ctx) : Ctx :=
  G.map (fun p => (p.1, subst_typ z u p.2))

-- [Coq: Dot_top_bot.v line 773]
def subst_fvar (x : Var) (y : Var) (z : Var) : Var := if z = x then y else z

-- ######################################################################
-- Operational Semantics

-- [Coq: Dot_top_bot.v lines 194-209]
inductive Red : Trm → Sto → Trm → Sto → Prop where
  | red_sel : ∀ x m s t T ds,
      Env.binds x (Val.val_new T ds) s →
      defs_has (open_defs x ds) (Defn.def_trm m t) →
      Red (Trm.trm_sel (Avar.avar_f x) m) s t s
  | red_app : ∀ f a s T t,
      Env.binds f (Val.val_lambda T t) s →
      Red (Trm.trm_app (Avar.avar_f f) (Avar.avar_f a)) s (open_trm a t) s
  | red_let : ∀ v t s x,
      x ∉ Env.dom s →
      Red (Trm.trm_let (Trm.trm_val v) t) s (open_trm x t) ((x, v) :: s)
  | red_let_var : ∀ t s x,
      Red (Trm.trm_let (Trm.trm_var (Avar.avar_f x)) t) s (open_trm x t) s
  | red_let_tgt : ∀ t0 t s t0' s',
      Red t0 s t0' s' →
      Red (Trm.trm_let t0 t) s (Trm.trm_let t0' t) s'

-- ######################################################################
-- Typing

-- [Coq: Dot_top_bot.v lines 214-216]
inductive Tymode : Type := | ty_precise | ty_general
inductive Submode : Type := | sub_tight | sub_general

mutual
  -- [Coq: Dot_top_bot.v lines 217-255]
  inductive TyTrm : Tymode → Submode → Ctx → Trm → Typ → Prop where
    | ty_var : ∀ (m1 : Tymode) (m2 : Submode) (G : Ctx) (x : Var) (T : Typ),
        Env.binds x T G →
        TyTrm m1 m2 G (Trm.trm_var (Avar.avar_f x)) T
    | ty_all_intro : ∀ (L : Vars) (m1 : Tymode) (m2 : Submode) (G : Ctx) (T : Typ) (t : Trm) (U : Typ),
        (∀ (x : Var), x ∉ L →
          TyTrm ty_general sub_general ((x, T) :: G) (open_trm x t) (open_typ x U)) →
        TyTrm m1 m2 G (Trm.trm_val (Val.val_lambda T t)) (Typ.typ_all T U)
    | ty_all_elim : ∀ (m2 : Submode) (G : Ctx) (x z : Var) (S T : Typ),
        TyTrm ty_general m2 G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_all S T) →
        TyTrm ty_general m2 G (Trm.trm_var (Avar.avar_f z)) S →
        TyTrm ty_general m2 G (Trm.trm_app (Avar.avar_f x) (Avar.avar_f z)) (open_typ z T)
    | ty_new_intro : ∀ (L : Vars) (m1 : Tymode) (m2 : Submode) (G : Ctx) (T : Typ) (ds : Defs),
        (∀ (x : Var), x ∉ L →
          TyDefs ((x, open_typ x T) :: G) (open_defs x ds) (open_typ x T)) →
        TyTrm m1 m2 G (Trm.trm_val (Val.val_new T ds)) (Typ.typ_bnd T)
    | ty_new_elim : ∀ (m2 : Submode) (G : Ctx) (x : Var) (m : TrmLabel) (T : Typ),
        TyTrm ty_general m2 G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_trm m T)) →
        TyTrm ty_general m2 G (Trm.trm_sel (Avar.avar_f x) m) T
    | ty_let : ∀ (L : Vars) (m2 : Submode) (G : Ctx) (t u : Trm) (T U : Typ),
        TyTrm ty_general m2 G t T →
        (∀ (x : Var), x ∉ L →
          TyTrm ty_general sub_general ((x, T) :: G) (open_trm x u) U) →
        TyTrm ty_general m2 G (Trm.trm_let t u) U
    | ty_rec_intro : ∀ (m2 : Submode) (G : Ctx) (x : Var) (T : Typ),
        TyTrm ty_general m2 G (Trm.trm_var (Avar.avar_f x)) (open_typ x T) →
        TyTrm ty_general m2 G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_bnd T)
    | ty_rec_elim : ∀ (m1 : Tymode) (m2 : Submode) (G : Ctx) (x : Var) (T : Typ),
        TyTrm m1 m2 G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_bnd T) →
        TyTrm m1 m2 G (Trm.trm_var (Avar.avar_f x)) (open_typ x T)
    | ty_and_intro : ∀ (m2 : Submode) (G : Ctx) (x : Var) (T U : Typ),
        TyTrm ty_general m2 G (Trm.trm_var (Avar.avar_f x)) T →
        TyTrm ty_general m2 G (Trm.trm_var (Avar.avar_f x)) U →
        TyTrm ty_general m2 G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_and T U)
    | ty_sub : ∀ (m1 : Tymode) (m2 : Submode) (G : Ctx) (t : Trm) (T U : Typ),
        (m1 = ty_precise → ∃ x, t = Trm.trm_var (Avar.avar_f x)) →
        TyTrm m1 m2 G t T →
        Subtyp ty_general m2 G T U →
        TyTrm m1 m2 G t U

  inductive TyDef : Ctx → Defn → Dec → Prop where
    | ty_def_typ : ∀ (G : Ctx) (A : TypLabel) (T : Typ),
        TyDef G (Defn.def_typ A T) (Dec.dec_typ A T T)
    | ty_def_trm : ∀ (G : Ctx) (a : TrmLabel) (t : Trm) (T : Typ),
        TyTrm ty_general sub_general G t T →
        TyDef G (Defn.def_trm a t) (Dec.dec_trm a T)

  inductive TyDefs : Ctx → Defs → Typ → Prop where
    | ty_defs_one : ∀ (G : Ctx) (d : Defn) (D : Dec),
        TyDef G d D →
        TyDefs G (Defs.defs_cons Defs.defs_nil d) (Typ.typ_rcd D)
    | ty_defs_cons : ∀ (G : Ctx) (ds : Defs) (d : Defn) (T : Typ) (D : Dec),
        TyDefs G ds T →
        TyDef G d D →
        defs_hasnt ds (label_of_def d) →
        TyDefs G (Defs.defs_cons ds d) (Typ.typ_and T (Typ.typ_rcd D))

  -- [Coq: Dot_top_bot.v lines 272-314] extended with top/bot
  inductive Subtyp : Tymode → Submode → Ctx → Typ → Typ → Prop where
    | subtyp_top : ∀ (m2 : Submode) (G : Ctx) (T : Typ),
        Subtyp ty_general m2 G T Typ.typ_top
    | subtyp_bot : ∀ (m2 : Submode) (G : Ctx) (T : Typ),
        Subtyp ty_general m2 G Typ.typ_bot T
    | subtyp_refl : ∀ (m2 : Submode) (G : Ctx) (T : Typ),
        Subtyp ty_general m2 G T T
    | subtyp_trans : ∀ (m1 : Tymode) (m2 : Submode) (G : Ctx) (S T U : Typ),
        Subtyp m1 m2 G S T →
        Subtyp m1 m2 G T U →
        Subtyp m1 m2 G S U
    | subtyp_and11 : ∀ (m1 : Tymode) (m2 : Submode) (G : Ctx) (T U : Typ),
        Subtyp m1 m2 G (Typ.typ_and T U) T
    | subtyp_and12 : ∀ (m1 : Tymode) (m2 : Submode) (G : Ctx) (T U : Typ),
        Subtyp m1 m2 G (Typ.typ_and T U) U
    | subtyp_and2 : ∀ (m2 : Submode) (G : Ctx) (S T U : Typ),
        Subtyp ty_general m2 G S T →
        Subtyp ty_general m2 G S U →
        Subtyp ty_general m2 G S (Typ.typ_and T U)
    | subtyp_fld : ∀ (m2 : Submode) (G : Ctx) (a : TrmLabel) (T U : Typ),
        Subtyp ty_general m2 G T U →
        Subtyp ty_general m2 G (Typ.typ_rcd (Dec.dec_trm a T)) (Typ.typ_rcd (Dec.dec_trm a U))
    | subtyp_typ : ∀ (m2 : Submode) (G : Ctx) (A : TypLabel) (S1 T1 S2 T2 : Typ),
        Subtyp ty_general m2 G S2 S1 →
        Subtyp ty_general m2 G T1 T2 →
        Subtyp ty_general m2 G (Typ.typ_rcd (Dec.dec_typ A S1 T1)) (Typ.typ_rcd (Dec.dec_typ A S2 T2))
    | subtyp_sel2 : ∀ (G : Ctx) (x : Var) (A : TypLabel) (S T : Typ),
        TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_typ A S T)) →
        Subtyp ty_general sub_general G S (Typ.typ_sel (Avar.avar_f x) A)
    | subtyp_sel1 : ∀ (G : Ctx) (x : Var) (A : TypLabel) (S T : Typ),
        TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_typ A S T)) →
        Subtyp ty_general sub_general G (Typ.typ_sel (Avar.avar_f x) A) T
    | subtyp_sel2_tight : ∀ (G : Ctx) (x : Var) (A : TypLabel) (T : Typ),
        TyTrm ty_precise sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_typ A T T)) →
        Subtyp ty_general sub_tight G T (Typ.typ_sel (Avar.avar_f x) A)
    | subtyp_sel1_tight : ∀ (G : Ctx) (x : Var) (A : TypLabel) (T : Typ),
        TyTrm ty_precise sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_typ A T T)) →
        Subtyp ty_general sub_tight G (Typ.typ_sel (Avar.avar_f x) A) T
    | subtyp_all : ∀ (L : Vars) (m2 : Submode) (G : Ctx) (S1 T1 S2 T2 : Typ),
        Subtyp ty_general m2 G S2 S1 →
        (∀ (x : Var), x ∉ L → Subtyp ty_general sub_general ((x, S2) :: G) (open_typ x T1) (open_typ x T2)) →
        Subtyp ty_general m2 G (Typ.typ_all S1 T1) (Typ.typ_all S2 T2)
end

-- [Coq: Dot_top_bot.v lines 316-324]
inductive WfSto : Ctx → Sto → Prop where
  | wf_sto_empty : WfSto [] []
  | wf_sto_push : ∀ (G : Ctx) (s : Sto) (x : Var) (T : Typ) (v : Val),
      WfSto G s → x ∉ Env.dom G → x ∉ Env.dom s →
      TyTrm ty_precise sub_general G (Trm.trm_val v) T →
      WfSto ((x, T) :: G) ((x, v) :: s)

-- (Optional) record machinery reused from Dot
inductive RecordDec : Dec → Prop where
  | rd_typ : ∀ A T, RecordDec (Dec.dec_typ A T T)
  | rd_trm : ∀ a T, RecordDec (Dec.dec_trm a T)

inductive RecordTyp : Typ → Finset Label → Prop where
  | rt_one : ∀ D l,
      RecordDec D → l = label_of_dec D → RecordTyp (Typ.typ_rcd D) {l}
  | rt_cons : ∀ T ls D l,
      RecordTyp T ls → RecordDec D → l = label_of_dec D → l ∉ ls →
      RecordTyp (Typ.typ_and T (Typ.typ_rcd D)) (ls ∪ {l})

-- A simple notion of record types
def record_type (T : Typ) : Prop := ∃ ls, RecordTyp T ls

  -- Record-Sub (subset; adapted)
  inductive RecordSub : Typ → Typ → Prop where
    | rs_refl : ∀ T, RecordSub T T
    | rs_dropl : ∀ T T' D, RecordSub T T' → RecordSub (Typ.typ_and T (Typ.typ_rcd D)) (Typ.typ_rcd D)
    | rs_drop : ∀ T T' D, RecordSub T T' → RecordSub (Typ.typ_and T (Typ.typ_rcd D)) T'
    | rs_pick : ∀ T T' D, RecordSub T T' → RecordSub (Typ.typ_and T (Typ.typ_rcd D)) (Typ.typ_and T' (Typ.typ_rcd D))


-- Has-member family (subset; adapted from Dot)
mutual
  inductive HasMember : Ctx → Var → Typ → TypLabel → Typ → Typ → Prop where
    | has_any : ∀ (G : Ctx) (x : Var) (T : Typ) (A : TypLabel) (S U : Typ),
        TyTrm ty_general sub_tight G (Trm.trm_var (Avar.avar_f x)) T →
        HasMemberRules G x T A S U →
        HasMember G x T A S U

  inductive HasMemberRules : Ctx → Var → Typ → TypLabel → Typ → Typ → Prop where
    | has_refl : ∀ (G : Ctx) (x : Var) (A : TypLabel) (S U : Typ),
        HasMemberRules G x (Typ.typ_rcd (Dec.dec_typ A S U)) A S U
    | has_and1 : ∀ (G : Ctx) (x : Var) (T1 T2 : Typ) (A : TypLabel) (S U : Typ),
        HasMember G x T1 A S U → HasMemberRules G x (Typ.typ_and T1 T2) A S U
    | has_and2 : ∀ (G : Ctx) (x : Var) (T1 T2 : Typ) (A : TypLabel) (S U : Typ),
        HasMember G x T2 A S U → HasMemberRules G x (Typ.typ_and T1 T2) A S U
    | has_bnd : ∀ (G : Ctx) (x : Var) (T : Typ) (A : TypLabel) (S U : Typ),
        HasMember G x (open_typ x T) A S U → HasMemberRules G x (Typ.typ_bnd T) A S U
    | has_sel : ∀ (G : Ctx) (x y : Var) (B : TypLabel) (T' : Typ) (A : TypLabel) (S U : Typ),
        TyTrm ty_precise sub_general G (Trm.trm_var (Avar.avar_f y)) (Typ.typ_rcd (Dec.dec_typ B T' T')) →
        HasMember G x T' A S U →
        HasMemberRules G x (Typ.typ_sel (Avar.avar_f y) B) A S U
    | has_bot : ∀ (G : Ctx) (x : Var) (A : TypLabel) (S U : Typ),
        HasMemberRules G x Typ.typ_bot A S U
end

-- Possible types (subset; adapted)
inductive PossibleTypes : Ctx → Var → Val → Typ → Prop where
  | pt_top : ∀ (G : Ctx) (x : Var) (v : Val), PossibleTypes G x v Typ.typ_top
  | pt_new : ∀ (G : Ctx) (x : Var) (T : Typ) (ds : Defs),
      PossibleTypes G x (Val.val_new T ds) (open_typ x T)
  | pt_rcd_trm : ∀ (G : Ctx) (x : Var) (T : Typ) (ds : Defs) (a : TrmLabel) (t : Trm) (T' : Typ),
      defs_has (open_defs x ds) (Defn.def_trm a t) →
      TyTrm ty_general sub_general G t T' →
      PossibleTypes G x (Val.val_new T ds) (Typ.typ_rcd (Dec.dec_trm a T'))
  | pt_rcd_typ : ∀ (G : Ctx) (x : Var) (T : Typ) (ds : Defs) (A : TypLabel) (T' S U : Typ),
      defs_has (open_defs x ds) (Defn.def_typ A T') →
      Subtyp ty_general sub_general G S T' →
      Subtyp ty_general sub_general G T' U →
      PossibleTypes G x (Val.val_new T ds) (Typ.typ_rcd (Dec.dec_typ A S U))
  | pt_lambda : ∀ (L : Vars) (G : Ctx) (x : Var) (S : Typ) (t : Trm) (T S' T' : Typ),
      (∀ (y : Var), y ∉ L → TyTrm ty_general sub_general ((y, S) :: G) (open_trm y t) (open_typ y T)) →
      Subtyp ty_general sub_general G S' S →
      (∀ (y : Var), y ∉ L → Subtyp ty_general sub_general ((y, S') :: G) (open_typ y T) (open_typ y T')) →
      PossibleTypes G x (Val.val_lambda S t) (Typ.typ_all S' T')
  | pt_and : ∀ (G : Ctx) (x : Var) (v : Val) (S1 S2 : Typ),
      PossibleTypes G x v S1 → PossibleTypes G x v S2 → PossibleTypes G x v (Typ.typ_and S1 S2)
  | pt_sel : ∀ (G : Ctx) (x : Var) (v : Val) (y : Avar) (A : TypLabel) (S : Typ),
      PossibleTypes G x v S → TyTrm ty_precise sub_general G (Trm.trm_var y) (Typ.typ_rcd (Dec.dec_typ A S S)) →
      PossibleTypes G x v (Typ.typ_sel y A)
  | pt_bnd : ∀ (G : Ctx) (x : Var) (v : Val) (S S' : Typ),
      PossibleTypes G x v S → S = open_typ x S' → PossibleTypes G x v (Typ.typ_bnd S')

-- Record-Has (subset; adapted)
inductive RecordHas : Typ → Dec → Prop where
  | rh_one : ∀ D, RecordHas (Typ.typ_rcd D) D
  | rh_andl : ∀ T D, RecordHas (Typ.typ_and T (Typ.typ_rcd D)) D
  | rh_and : ∀ T D D', RecordHas T D' → RecordHas (Typ.typ_and T D) D'

-- Normal forms (subset; adapted)
inductive NormalForm : Trm → Prop where
  | nf_var : ∀ (x : Avar), NormalForm (Trm.trm_var x)
  | nf_val : ∀ (v : Val), NormalForm (Trm.trm_val v)

end Lp2lc.Active.Dot_top_bot
