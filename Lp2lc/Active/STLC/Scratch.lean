import Std

example : Type 1 := Type
example : Type 1 := Type -> Type

inductive Box0 (T : Type) : Type where
  | mk : (v: T) -> Box0 T

inductive Box1 : (T: Type) -> Type where
  | mk : {T: Type} -> (v: T) -> Box1 T

inductive Box3 : Type 1 where
  | mk : {T: Type} -> (v: T) -> Box3
def Box3AlsoMk {T: Type} (v: T) : Box3 := Box3.mk v

inductive Box4 : Type 1 where
  | mk {T: Type} : (v: T) -> Box4
def Box4AlsoMk {T: Type} (v: T) : Box4 := Box4.mk v

example : {T : Type} -> T -> Box3 := Box3.mk
example : {T : Type} -> T -> Box3 := Box3AlsoMk
example : {T : Type} -> T -> Box4 := Box4.mk
example : {T : Type} -> T -> Box4 := Box4AlsoMk

inductive Sys (typ: Type) (trm: Type) : Type where
| mk : Sys typ trm


example : Type -> Type -> Type := Sys

def SigmaLike (T : Type) : Type :=
  @Sigma (List T) (fun (_ : List T) => T -> Prop)


-- structure Sys2 where
--   typ: Type
--   trm: Type

-- example: Type -> Type -> Type := Sys2
