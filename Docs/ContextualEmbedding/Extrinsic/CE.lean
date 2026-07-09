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

inductive Index : Ctx -> Type where
  | Top {ts : Ctx} {t : Ty} : Index (ts :/: t)
  | Pop {ts : Ctx} {t' : Ty} : Index ts -> Index (ts :/: t')
deriving Repr, DecidableEq
open Index

inductive STLC : Ctx -> Type where
  | Var (i : Index ts) : STLC ts
  | Star : STLC ts
  | Lambda (a : Ty) (body : STLC (ts :/: a)) : STLC ts
  | Apply (fn : STLC ts) (arg : STLC ts) : STLC ts
deriving Repr, DecidableEq
open STLC

inductive Lookup : (ts : Ctx) -> Index ts -> Ty -> Type where
  | Top {ts : Ctx} {t : Ty} : Lookup (ts :/: t) Top t
  | Pop {ts : Ctx} {t t' : Ty} {i : Index ts} : Lookup ts i t -> Lookup (ts :/: t') (Pop i) t
deriving Repr

inductive HasType : (ts : Ctx) -> STLC ts -> Ty -> Type where
  | Var : Lookup ts i t -> HasType ts (Var i) t
  | Star : HasType ts Star Unit
  | Lambda : HasType (ts :/: t1) e t2 -> HasType ts (Lambda t1 e) (t1 :-> t2)
  | Apply : HasType ts e1 (t1 :-> t2) -> HasType ts e2 t1 -> HasType ts (Apply e1 e2) t2
deriving Repr

inductive ProxyTop : Ctx -> Type where
  | PTop {ts : Ctx} {t : Ty} : ProxyTop (ts :/: t)
deriving Repr, DecidableEq
open ProxyTop

class ReifyIndex (ts : Ctx) (ts' : Ctx) where
  reify : ProxyTop ts -> Index ts'
open ReifyIndex

instance instReifyIndexRefl : ReifyIndex ts ts where
  reify
    | PTop => Top

instance instReifyIndexSnoc [instRec : ReifyIndex ts1 ts2] : ReifyIndex ts1 (ts2 :/: t') where
  reify := fun i => Pop (ReifyIndex.reify i)

inductive STLCCtx : Ctx -> Type where
  | CVar {ts ts' : Ctx} [inst : ReifyIndex ts ts'] (proxy : ProxyTop ts) : STLCCtx ts'
  | CStar : STLCCtx ts
  | CLam {ts : Ctx} (a : Ty) (body : ProxyTop (ts :/: a) -> STLCCtx (ts :/: a)) : STLCCtx ts
  | CApp (fn : STLCCtx ts) (arg : STLCCtx ts) : STLCCtx ts
open STLCCtx


-- Unembed
-----------

def unembed : STLCCtx ts -> STLC ts
  | STLCCtx.CStar => STLC.Star
  | @STLCCtx.CVar _ _ _ proxy => STLC.Var (ReifyIndex.reify proxy)
  | @STLCCtx.CLam ts a body => STLC.Lambda a (unembed (body (@PTop ts a)))
  | STLCCtx.CApp e1 e2 => STLC.Apply (unembed e1) (unembed e2)


-- Contextualise
-----------------

inductive ProxyVar ts' where
  | PVar [inst : ReifyIndex ts ts'] : ProxyTop ts -> ProxyVar ts'
deriving Repr
open ProxyVar

def weakenPVar : ProxyVar ts' -> ProxyVar (ts' :/: t')
  | @PVar _ _ _ proxy =>
      PVar proxy

def varTop : ProxyVar (ts :/: t) :=
  PVar (@PTop ts t)

def fromVar : ProxyVar ts' -> STLCCtx ts'
  | @PVar _ _ _ proxy => STLCCtx.CVar proxy

def fromIndex : Index ts -> ProxyVar ts
  | Top => varTop
  | Pop i => weakenPVar (fromIndex i)

def toCVar : Index ts -> STLCCtx ts :=
  fun i => fromVar (fromIndex i)

def contextualise : STLC ts -> STLCCtx ts
  | STLC.Var i => toCVar i
  | STLC.Lambda a e => STLCCtx.CLam a (fun _ => contextualise e)
  | STLC.Apply e1 e2 => STLCCtx.CApp (contextualise e1) (contextualise e2)
  | STLC.Star => STLCCtx.CStar

--------------------------------------------
--           Isomorphism proofs           --
--------------------------------------------

theorem indexIsoL (i : Index ts)
  : ReifyIndex.reify (self := (fromIndex i).2) (fromIndex i).3 = i := by
  induction i with
  | Top => rfl
  | Pop i' ih =>
      change Pop (ReifyIndex.reify (self := (fromIndex i').2) (fromIndex i').3) = Pop i'
      exact congrArg Pop ih

axiom closedWorld {ts1 ts2 : Ctx} (inst : ReifyIndex ts1 ts2)
  : (∃ hEq : ts1 = ts2, hEq ▸ inst = instReifyIndexRefl)
    \/
    (∃ (ts2' : Ctx) (t : Ty) (hEq : ts2 = ts2' :/: t) (inst' : ReifyIndex ts1 ts2'),
      hEq ▸ inst = instReifyIndexSnoc (instRec := inst'))

theorem unembedToCVar (i : Index ts) : unembed (toCVar i) = STLC.Var i := by
  induction i with
  | Top => rfl
  | Pop i' ih =>
      change STLC.Var (Index.Pop (ReifyIndex.reify (self := (fromIndex i').2) (fromIndex i').3)) =
        STLC.Var (Index.Pop i')
      exact congrArg (fun index => STLC.Var (Index.Pop index)) (indexIsoL i')

theorem indexIsoR (inst : ReifyIndex ts ts') (i : ProxyTop ts)
  : fromIndex (ReifyIndex.reify (self := inst) i) = PVar (inst := inst) i :=
  Or.elim (closedWorld inst)
    (fun h => by
      rcases h with ⟨hEq, instEqRefl⟩
      subst hEq
      simp at instEqRefl
      rw [instEqRefl]
      cases i
      rfl)
    (fun h => by
      rcases h with ⟨ts2', t', hEq, inst', instEqSnoc⟩
      subst hEq
      simp at instEqSnoc
      rw [instEqSnoc]
      change weakenPVar (fromIndex (ReifyIndex.reify (self := inst') i)) =
        weakenPVar (PVar (inst := inst') i)
      rw [indexIsoR inst' i])

theorem isoL {e : STLC ts}
  : unembed (contextualise e) = e := by
  induction e with
  | Star => rfl
  | Apply e1 e2 ih1 ih2 => simp [contextualise, unembed, ih1, ih2]
  | Lambda a body ih => simp [contextualise, unembed, ih]
  | Var i =>
      simp [contextualise, toCVar, fromVar, unembed]
      exact indexIsoL i

theorem isoL' {e : STLC ts}
  : unembed (contextualise e) = e := by
  induction e
    <;> simp [contextualise, unembed, *]
  case Var i =>
    simp [toCVar, fromVar, unembed]
    exact indexIsoL i

theorem isoR {e : STLCCtx ts}
  : contextualise (unembed e) = e := by
  induction e with
  | CStar => rfl
  | CApp e1 e2 ih1 ih2 =>
      simp [unembed, contextualise, ih1, ih2]
  | @CVar _ _ inst proxy =>
      simp [unembed, contextualise, toCVar]
      rw [indexIsoR inst proxy]
      rfl
  | CLam a body ih =>
      simp [unembed, contextualise]
      funext x
      cases x
      simp [ih]

theorem isoR' {e : STLCCtx ts}
  : contextualise (unembed e) = e := by
  induction e
    <;> try (simp [contextualise, unembed, *])
    <;> try (repeat' (funext p; cases p)
             <;> simp [*])
  case CVar => simp [toCVar, indexIsoR]
               rfl

-- Examples
------------

def showSTLCCtx : STLCCtx ts -> String
  | @STLCCtx.CVar _ _ inst proxy => "CVar " ++ reprStr proxy ++ "[reified = " ++ reprStr (ReifyIndex.reify (self := inst) proxy) ++ "]"
  | STLCCtx.CStar => "CStar"
  | @STLCCtx.CLam ts a body => "CLam (\\<ProxyTop> -> " ++ showSTLCCtx (body (@PTop ts a)) ++ ")"
  | STLCCtx.CApp f x => "CApp (" ++ showSTLCCtx f ++ ") (" ++ showSTLCCtx x ++ ")"

def idSTLC {ts : Ctx} {a : Ty} : STLCCtx ts :=
  STLCCtx.CLam a (fun x => STLCCtx.CVar x)

def idSTLC' := @idSTLC Ctx.Empty Unit

#check idSTLC
#eval showSTLCCtx idSTLC'
#eval unembed idSTLC'
#eval showSTLCCtx (contextualise (unembed idSTLC'))
#eval unembed (contextualise (unembed idSTLC'))

def const {ts : Ctx} {a b : Ty} : STLCCtx ts :=
  STLCCtx.CLam a
    (fun x => STLCCtx.CLam b
      (fun _y => STLCCtx.CVar x))

def const' := @const Ctx.Empty Unit Unit

#eval showSTLCCtx const'
#eval unembed const'
#eval showSTLCCtx (contextualise (unembed const'))
#eval unembed (contextualise (unembed const'))

def flipConst {ts : Ctx} {a b : Ty} : STLCCtx ts :=
  STLCCtx.CLam a
    (fun _x => STLCCtx.CLam b
      (fun y => STLCCtx.CVar y))

def flipConst' := @flipConst Ctx.Empty Unit Unit

#check flipConst
#eval showSTLCCtx flipConst'
#eval unembed flipConst'
#eval showSTLCCtx (contextualise (unembed flipConst'))
#eval unembed (contextualise (unembed flipConst'))

def const5 {ts : Ctx} {a b c d e : Ty} : STLCCtx ts :=
  STLCCtx.CLam a (fun x1 =>
    STLCCtx.CLam b (fun _x2 =>
      STLCCtx.CLam c (fun _x3 =>
        STLCCtx.CLam d (fun _x4 =>
          STLCCtx.CLam e (fun _x5 =>
            STLCCtx.CVar x1)))))

def const5' := @const5 Ctx.Empty Unit Unit Unit Unit Unit

#eval showSTLCCtx const5'
#eval unembed const5'
#eval showSTLCCtx (contextualise (unembed const5'))
#eval unembed (contextualise (unembed const5'))


-- Examples in theorems
------------------------

example {ts : Ctx} {a : Ty}
  : (STLCCtx.CLam a (fun x => STLCCtx.CVar x) : STLCCtx ts) =
    (STLCCtx.CLam a (fun y => STLCCtx.CVar y) : STLCCtx ts) := by
  rfl

example {ts : Ctx} {a : Ty}
  : (contextualise (STLC.Lambda a (STLC.Var Index.Top)) : STLCCtx ts) =
    (STLCCtx.CLam a (fun y => STLCCtx.CVar y) : STLCCtx ts) := by
  simp [contextualise, toCVar, fromIndex, fromVar]
  funext x
  cases x
  rfl

end ContextualEmbedding.Extrinsic.CE
