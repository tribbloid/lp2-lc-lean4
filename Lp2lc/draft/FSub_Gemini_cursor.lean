import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

import Aesop

inductive Typ : Type where
  | top : Typ
  | bvar : Nat → Typ
  | fvar : String → Typ
  | arrow : Typ → Typ → Typ
  | all : Typ → Typ → Typ
deriving DecidableEq

inductive Trm : Type where
  | bvar : Nat → Trm
  | fvar : String → Trm
  | abs  : Typ → Trm → Trm
  | app  : Trm → Trm → Trm
  | tabs : Typ → Trm → Trm
  | tapp : Trm → Typ → Trm

def openTtRec (K : Nat) (U : Typ) (T : Typ) : Typ :=
  match T with
  | Typ.top => Typ.top
  | Typ.bvar J => if K = J then U else (Typ.bvar J)
  | Typ.fvar X => Typ.fvar X
  | Typ.arrow T1 T2 => Typ.arrow (openTtRec K U T1) (openTtRec K U T2)
  | Typ.all T1 T2 => Typ.all (openTtRec K U T1) (openTtRec (K + 1) U T2)

def openTt (T : Typ) (U : Typ) : Typ := openTtRec 0 U T

def openTeRec (K : Nat) (U : Typ) (e : Trm) : Trm :=
  match e with
  | Trm.bvar i    => Trm.bvar i
  | Trm.fvar x    => Trm.fvar x
  | Trm.abs V e1  => Trm.abs  (openTtRec K U V)  (openTeRec K U e1)
  | Trm.app e1 e2 => Trm.app  (openTeRec K U e1) (openTeRec K U e2)
  | Trm.tabs V e1 => Trm.tabs (openTtRec K U V)  (openTeRec (K + 1) U e1)
  | Trm.tapp e1 V => Trm.tapp (openTeRec K U e1) (openTtRec K U V)

def openTe (t : Trm) (U : Typ) : Trm := openTeRec 0 U t

def openEeRec (k : Nat) (f : Trm) (e : Trm) : Trm :=
  match e with
  | Trm.bvar i    => if k = i then f else (Trm.bvar i)
  | Trm.fvar x    => Trm.fvar x
  | Trm.abs V e1  => Trm.abs V (openEeRec (k + 1) f e1)
  | Trm.app e1 e2 => Trm.app (openEeRec k f e1) (openEeRec k f e2)
  | Trm.tabs V e1 => Trm.tabs V (openEeRec k f e1)
  | Trm.tapp e1 V => Trm.tapp (openEeRec k f e1) V

def openEe (e : Trm) (f : Trm) : Trm := openEeRec 0 f e

def openTtVar (T : Typ) (X : String) : Typ := openTt T (Typ.fvar X)
def openTeVar (t : Trm) (X : String) : Trm := openTe t (Typ.fvar X)
def openEeVar (t : Trm) (x : String) : Trm := openEe t (Trm.fvar x)

inductive IsType : Typ → Prop where
  | top : IsType Typ.top
  | fvar (X : String) : IsType (Typ.fvar X)
  | arrow (T1 T2 : Typ) :
      IsType T1 →
      IsType T2 →
      IsType (Typ.arrow T1 T2)
  | all (L : List String) (T1 T2 : Typ) :
      IsType T1 →
      (∀ (X : String), X ∉ L → IsType (openTtVar T2 X)) →
      IsType (Typ.all T1 T2)

inductive IsTerm : Trm → Prop where
  | fvar (x : String) : IsTerm (Trm.fvar x)
  | abs (L : List String) (V : Typ) (e1 : Trm) :
      IsType V →
      (∀ (x : String), x ∉ L → IsTerm (openEeVar e1 x)) →
      IsTerm (Trm.abs V e1)
  | app (e1 e2 : Trm) :
      IsTerm e1 →
      IsTerm e2 →
      IsTerm (Trm.app e1 e2)
  | tabs (L : List String) (V : Typ) (e1 : Trm) :
      IsType V →
      (∀ (X : String), X ∉ L → IsTerm (openTeVar e1 X)) →
      IsTerm (Trm.tabs V e1)
  | tapp (e1 : Trm) (V : Typ) :
      IsTerm e1 →
      IsType V →
      IsTerm (Trm.tapp e1 V)

inductive Binding : Type where
  | sub : Typ → Binding
  | typ : Typ → Binding
deriving DecidableEq

def Context := List (String × Binding)

inductive WfTyp : Context → Typ → Prop where
  | top (Γ : Context) : WfTyp Γ Typ.top
  | var (U : Typ) (Γ : Context) (X : String) :
      (X, Binding.sub U) ∈ Γ →
      WfTyp Γ (Typ.fvar X)
  | arrow (Γ : Context) (T1 T2 : Typ) :
      WfTyp Γ T1 →
      WfTyp Γ T2 →
      WfTyp Γ (Typ.arrow T1 T2)
  | all (L : List String) (Γ : Context) (T1 T2 : Typ) :
      WfTyp Γ T1 →
      (∀ (X : String), X ∉ L → WfTyp ((X, Binding.sub T1) :: Γ) (openTtVar T2 X)) →
      WfTyp Γ (Typ.all T1 T2)

inductive OkContext : Context → Prop where
  | empty : OkContext []
  | sub (Γ : Context) (X : String) (T : Typ) :
      OkContext Γ →
      WfTyp Γ T →
      X ∉ (Γ.map Prod.fst) →
      OkContext ((X, Binding.sub T) :: Γ)
  | typ (Γ : Context) (x : String) (T : Typ) :
      OkContext Γ →
      WfTyp Γ T →
      x ∉ (Γ.map Prod.fst) →
      OkContext ((x, Binding.typ T) :: Γ)

inductive IsSubtype : Context → Typ → Typ → Prop where
  | top (Γ : Context) (S : Typ) :
      OkContext Γ →
      WfTyp Γ S →
      IsSubtype Γ S Typ.top
  | refl_fvar (Γ : Context) (X : String) :
      OkContext Γ →
      WfTyp Γ (Typ.fvar X) →
      IsSubtype Γ (Typ.fvar X) (Typ.fvar X)
  | trans_fvar (U : Typ) (Γ : Context) (T : Typ) (X : String) :
      (X, Binding.sub U) ∈ Γ →
      IsSubtype Γ U T →
      IsSubtype Γ (Typ.fvar X) T
  | arrow (Γ : Context) (S1 S2 T1 T2 : Typ) :
      IsSubtype Γ T1 S1 →
      IsSubtype Γ S2 T2 →
      IsSubtype Γ (Typ.arrow S1 S2) (Typ.arrow T1 T2)
  | all (L : List String) (Γ : Context) (S1 S2 T1 T2 : Typ) :
      IsSubtype Γ T1 S1 →
      (∀ (X : String), X ∉ L →
          IsSubtype ((X, Binding.sub T1) :: Γ) (openTtVar S2 X) (openTtVar T2 X)) →
      IsSubtype Γ (Typ.all S1 S2) (Typ.all T1 T2)
