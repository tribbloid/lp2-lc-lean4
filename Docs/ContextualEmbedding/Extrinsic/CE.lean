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

instance instReifyIndexRefl : ReifyIndex (ts :/: t) (ts :/: t) where
  reify
    | PTop => Top

instance instReifyIndexSnoc [instRec : ReifyIndex ts1 ts2] : ReifyIndex ts1 (ts2 :/: t') where
  reify := fun i => Pop (ReifyIndex.reify (self := instRec) i)

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
  | @STLCCtx.CVar _ _ inst proxy => STLC.Var (ReifyIndex.reify (self := inst) proxy)
  | @STLCCtx.CLam ts a body => STLC.Lambda a (unembed (body (@PTop ts a)))
  | STLCCtx.CApp e1 e2 => STLC.Apply (unembed e1) (unembed e2)


-- Contextualise
-----------------

inductive ProxyVar ts' where
  | PVar [inst : ReifyIndex ts ts'] : ProxyTop ts -> ProxyVar ts'
deriving Repr
open ProxyVar

def weakenPVar : ProxyVar ts' -> ProxyVar (ts' :/: t')
  | @PVar _ _ inst proxy =>
      PVar (inst := instReifyIndexSnoc (instRec := inst)) proxy

def varTop : ProxyVar (ts :/: t) :=
  PVar (inst := instReifyIndexRefl) (@PTop ts t)

def fromVar : ProxyVar ts' -> STLCCtx ts'
  | @PVar _ _ inst proxy => STLCCtx.CVar (inst := inst) proxy

def fromIndex : Index ts -> ProxyVar ts
  | Top => varTop
  | Pop i => weakenPVar (fromIndex i)

def toCVar : Index ts -> STLCCtx ts :=
  fun i => fromVar (fromIndex i)

inductive CtxHasType : (ts : Ctx) -> STLCCtx ts -> Ty -> Type where
  | CVar : (lookup : Lookup ts i t) -> CtxHasType ts (toCVar i) t
  | CStar : CtxHasType ts CStar Unit
  | CLam : ((proxy : ProxyTop (ts :/: a)) -> CtxHasType (ts :/: a) (body proxy) b) ->
      CtxHasType ts (CLam (ts := ts) a body) (a :-> b)
  | CApp : CtxHasType ts e1 (a :-> b) -> CtxHasType ts e2 a -> CtxHasType ts (CApp e1 e2) b

def contextualise : STLC ts -> STLCCtx ts
  | STLC.Var i => toCVar i
  | STLC.Lambda a e => STLCCtx.CLam (ts := ts) a (fun _ => contextualise e)
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

theorem unembedToCVar (i : Index ts) : unembed (toCVar i) = STLC.Var i := by
  induction i with
  | Top => rfl
  | Pop i' ih =>
      change STLC.Var (Index.Pop (ReifyIndex.reify (self := (fromIndex i').2) (fromIndex i').3)) =
        STLC.Var (Index.Pop i')
      exact congrArg (fun index => STLC.Var (Index.Pop index)) (indexIsoL i')

theorem indexIsoR (i : Index ts)
  : contextualise (STLC.Var i) = toCVar i := by
  rfl

def unembedTyped : CtxHasType ts e t -> HasType ts (unembed e) t
  | CtxHasType.CVar lookup => by
      rw [unembedToCVar]
      exact HasType.Var lookup
  | CtxHasType.CStar => HasType.Star
  | @CtxHasType.CLam ts a _ _ bodyTyped =>
      HasType.Lambda (unembedTyped (bodyTyped (@PTop ts a)))
  | CtxHasType.CApp e1 e2 => HasType.Apply (unembedTyped e1) (unembedTyped e2)

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

theorem isoR {h : CtxHasType ts e t}
  : contextualise (unembed e) = e := by
  induction h with
  | CVar lookup =>
      rw [unembedToCVar]
      rfl
  | CStar => rfl
  | CLam bodyTyped ih =>
      simp [unembed, contextualise]
      funext x
      cases x
      simp [ih]
  | CApp e1 e2 ih1 ih2 =>
      simp [unembed, contextualise, ih1, ih2]

theorem isoR' {h : CtxHasType ts e t}
  : contextualise (unembed e) = e := isoR (h := h)

-- Examples
------------

def showSTLCCtx : STLCCtx ts -> String
  | @STLCCtx.CVar _ _ inst proxy => "CVar " ++ reprStr proxy ++ "[reified = " ++ reprStr (ReifyIndex.reify (self := inst) proxy) ++ "]"
  | STLCCtx.CStar => "CStar"
  | @STLCCtx.CLam ts a body => "CLam (\\<ProxyTop> -> " ++ showSTLCCtx (body (@PTop ts a)) ++ ")"
  | STLCCtx.CApp f x => "CApp (" ++ showSTLCCtx f ++ ") (" ++ showSTLCCtx x ++ ")"

def idSTLC {ts : Ctx} {a : Ty} : STLCCtx ts :=
  STLCCtx.CLam (ts := ts) a (fun x => STLCCtx.CVar (ts' := ts :/: a) x)

def idSTLCTyped {ts : Ctx} {a : Ty} : CtxHasType ts (@idSTLC ts a) (a :-> a) :=
  CtxHasType.CLam (fun x => by
    cases x
    exact CtxHasType.CVar Lookup.Top)

def idSTLC' := @idSTLC Ctx.Empty Unit
def idSTLCTyped' := @idSTLCTyped Ctx.Empty Unit

#check idSTLC
#eval showSTLCCtx idSTLC'
#eval unembed idSTLC'
#eval showSTLCCtx (contextualise (unembed idSTLC'))
#eval unembed (contextualise (unembed idSTLC'))

def const {ts : Ctx} {a b : Ty} : STLCCtx ts :=
  STLCCtx.CLam (ts := ts) a
    (fun x => STLCCtx.CLam (ts := ts :/: a) b
      (fun _y => STLCCtx.CVar (ts' := (ts :/: a) :/: b) x))

def constTyped {ts : Ctx} {a b : Ty} : CtxHasType ts (@const ts a b) (a :-> b :-> a) :=
  CtxHasType.CLam (fun x => by
    cases x
    exact CtxHasType.CLam (fun _y =>
      CtxHasType.CVar (Lookup.Pop Lookup.Top)))

def const' := @const Ctx.Empty Unit Unit
def constTyped' := @constTyped Ctx.Empty Unit Unit

#eval showSTLCCtx const'
#eval unembed const'
#eval showSTLCCtx (contextualise (unembed const'))
#eval unembed (contextualise (unembed const'))

def flipConst {ts : Ctx} {a b : Ty} : STLCCtx ts :=
  STLCCtx.CLam (ts := ts) a
    (fun _x => STLCCtx.CLam (ts := ts :/: a) b
      (fun y => STLCCtx.CVar (ts' := (ts :/: a) :/: b) y))

def flipConstTyped {ts : Ctx} {a b : Ty} : CtxHasType ts (@flipConst ts a b) (a :-> b :-> b) :=
  CtxHasType.CLam (fun _x =>
    CtxHasType.CLam (fun y => by
      cases y
      exact CtxHasType.CVar Lookup.Top))

def flipConst' := @flipConst Ctx.Empty Unit Unit
def flipConstTyped' := @flipConstTyped Ctx.Empty Unit Unit

#check flipConst
#eval showSTLCCtx flipConst'
#eval unembed flipConst'
#eval showSTLCCtx (contextualise (unembed flipConst'))
#eval unembed (contextualise (unembed flipConst'))

def const5 {ts : Ctx} {a b c d e : Ty} : STLCCtx ts :=
  STLCCtx.CLam (ts := ts) a (fun x1 =>
    STLCCtx.CLam (ts := ts :/: a) b (fun _x2 =>
      STLCCtx.CLam (ts := (ts :/: a) :/: b) c (fun _x3 =>
        STLCCtx.CLam (ts := ((ts :/: a) :/: b) :/: c) d (fun _x4 =>
          STLCCtx.CLam (ts := (((ts :/: a) :/: b) :/: c) :/: d) e (fun _x5 =>
            STLCCtx.CVar (ts' := ((((ts :/: a) :/: b) :/: c) :/: d) :/: e) x1)))))

def const5Typed {ts : Ctx} {a b c d e : Ty} :
    CtxHasType ts (@const5 ts a b c d e) (a :-> b :-> c :-> d :-> e :-> a) :=
  CtxHasType.CLam (fun x1 => by
    cases x1
    exact CtxHasType.CLam (fun _x2 =>
      CtxHasType.CLam (fun _x3 =>
        CtxHasType.CLam (fun _x4 =>
          CtxHasType.CLam (fun _x5 =>
            CtxHasType.CVar
              (Lookup.Pop (Lookup.Pop (Lookup.Pop (Lookup.Pop Lookup.Top)))))))))

def const5' := @const5 Ctx.Empty Unit Unit Unit Unit Unit
def const5Typed' := @const5Typed Ctx.Empty Unit Unit Unit Unit Unit

#eval showSTLCCtx const5'
#eval unembed const5'
#eval showSTLCCtx (contextualise (unembed const5'))
#eval unembed (contextualise (unembed const5'))


-- Examples in theorems
------------------------

example {ts : Ctx} {a : Ty}
  : @STLCCtx.CLam ts a (fun x => STLCCtx.CVar (ts' := ts :/: a) x) =
    @STLCCtx.CLam ts a (fun y => STLCCtx.CVar (ts' := ts :/: a) y) := by
  rfl

example {ts : Ctx} {a : Ty}
  : @contextualise ts (STLC.Lambda a (STLC.Var Index.Top)) =
    @STLCCtx.CLam ts a (fun y => STLCCtx.CVar (ts' := ts :/: a) y) := by
  simp [contextualise, toCVar, fromIndex, fromVar]
  funext x
  cases x
  rfl

end ContextualEmbedding.Extrinsic.CE
