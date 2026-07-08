namespace ContextualEmbedding.Extrinsic.CE

/-
derived from CE.lean, but using extrinsic typing instead of intrinsic typing
-/

inductive Ty : Type
  | Unit : Ty
  | Fun : Ty -> Ty -> Ty
deriving Repr, DecidableEq
open Ty

infixr:90 " :-> " => Fun

inductive Ctx : Type
  | Empty : Ctx
  | Snoc : Ctx -> Ty -> Ctx
deriving Repr, DecidableEq

infixl:90 " :/: " => Ctx.Snoc

inductive Index : Type where
  | Top : Index
  | Pop : Index -> Index
deriving Repr, DecidableEq
open Index

inductive Lookup : Ctx -> Index -> Ty -> Type where
  | Top {ts : Ctx} {t : Ty} : Lookup (ts :/: t) Top t
  | Pop {ts : Ctx} {t t' : Ty} {i : Index} : Lookup ts i t -> Lookup (ts :/: t') (Pop i) t
deriving Repr

inductive STLC : Type where
  | Var : Index -> STLC
  | Star : STLC
  | Lambda : Ty -> STLC -> STLC
  | Apply : STLC -> STLC -> STLC
deriving Repr, DecidableEq
open STLC

inductive HasType : Ctx -> STLC -> Ty -> Type where
  | Var : Lookup ts i t -> HasType ts (Var i) t
  | Star : HasType ts Star Unit
  | Lambda : HasType (ts :/: t1) e t2 -> HasType ts (Lambda t1 e) (t1 :-> t2)
  | Apply : HasType ts e1 (t1 :-> t2) -> HasType ts e2 t1 -> HasType ts (Apply e1 e2) t2
deriving Repr

inductive ProxyTop : Ctx -> Type where
  | PTop {ts : Ctx} : ProxyTop ts
deriving Repr, DecidableEq
open ProxyTop

class ReifyIndex (ts : Ctx) (ts' : Ctx) where
  reify : ProxyTop ts -> Index
open ReifyIndex

instance instReifyIndexRefl : ReifyIndex (ts :/: t) (ts :/: t) where
  reify
    | PTop => Top

instance instReifyIndexSnoc [instRec : ReifyIndex ts1 ts2] : ReifyIndex ts1 (ts2 :/: t') where
  reify := fun i => Pop (ReifyIndex.reify ts2 (self := instRec) i)

end ContextualEmbedding.CEExtrinsic
