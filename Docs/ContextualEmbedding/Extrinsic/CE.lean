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

inductive STLC : Type where
  | Var : Index -> STLC
  | Star : STLC
  | Lambda : Ty -> STLC -> STLC
  | Apply : STLC -> STLC -> STLC
deriving Repr, DecidableEq
open STLC

inductive Lookup : Ctx -> Index -> Ty -> Type where
  | Top {ts : Ctx} {t : Ty} : Lookup (ts :/: t) Top t
  | Pop {ts : Ctx} {t t' : Ty} {i : Index} : Lookup ts i t -> Lookup (ts :/: t') (Pop i) t
deriving Repr

inductive HasType : Ctx -> STLC -> Ty -> Type where
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
  reify : ProxyTop ts -> Index
open ReifyIndex

instance instReifyIndexRefl : ReifyIndex (ts :/: t) (ts :/: t) where
  reify
    | PTop => Top

instance instReifyIndexSnoc [instRec : ReifyIndex ts1 ts2] : ReifyIndex ts1 (ts2 :/: t') where
  reify := fun i => Pop (ReifyIndex.reify ts2 (self := instRec) i)

inductive STLCCtx : Type where
  | CVar {ts ts' : Ctx} [inst : ReifyIndex ts ts'] : ProxyTop ts -> STLCCtx
  | CStar : STLCCtx
  | CLam {ts : Ctx} (a : Ty) : (ProxyTop (ts :/: a) -> STLCCtx) -> STLCCtx
  | CApp : STLCCtx -> STLCCtx -> STLCCtx
open STLCCtx


-- Unembed
-----------

def unembed : STLCCtx -> STLC
  | STLCCtx.CStar => STLC.Star
  | @STLCCtx.CVar _ ts' inst proxy => STLC.Var (ReifyIndex.reify ts' (self := inst) proxy)
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

def fromVar : ProxyVar ts' -> STLCCtx
  | @PVar _ _ inst proxy => STLCCtx.CVar (inst := inst) proxy

def fromIndex : Lookup ts i t -> ProxyVar ts
  | Lookup.Top => varTop
  | Lookup.Pop i => weakenPVar (fromIndex i)

def toCVar : Lookup ts i t -> STLCCtx :=
  fun i => fromVar (fromIndex i)

inductive CtxHasType : Ctx -> STLCCtx -> Ty -> Type where
  | CVar : (lookup : Lookup ts i t) -> CtxHasType ts (toCVar lookup) t
  | CStar : CtxHasType ts CStar Unit
  | CLam : ((proxy : ProxyTop (ts :/: a)) -> CtxHasType (ts :/: a) (body proxy) b) ->
      CtxHasType ts (CLam (ts := ts) a body) (a :-> b)
  | CApp : CtxHasType ts e1 (a :-> b) -> CtxHasType ts e2 a -> CtxHasType ts (CApp e1 e2) b

def contextualise : HasType ts e t -> STLCCtx
  | HasType.Var i => toCVar i
  | @HasType.Lambda ts a _ _ e => STLCCtx.CLam (ts := ts) a (fun _ => contextualise e)
  | HasType.Apply e1 e2 => STLCCtx.CApp (contextualise e1) (contextualise e2)
  | HasType.Star => STLCCtx.CStar

--------------------------------------------
--           Isomorphism proofs           --
--------------------------------------------

theorem indexIsoL (i : Lookup ts idx t)
  : ReifyIndex.reify ts (self := (fromIndex i).2) (fromIndex i).3 = idx := by
  induction i with
  | Top => rfl
  | Pop i' ih =>
      change Pop (ReifyIndex.reify _ (self := (fromIndex i').2) (fromIndex i').3) = Pop _
      exact congrArg Pop ih

theorem unembedToCVar (lookup : Lookup ts i t) : unembed (toCVar lookup) = STLC.Var i := by
  induction lookup with
  | Top => rfl
  | Pop lookup ih =>
      change STLC.Var (Index.Pop (ReifyIndex.reify _ (self := (fromIndex lookup).2) (fromIndex lookup).3)) =
        STLC.Var (Index.Pop _)
      exact congrArg (fun index => STLC.Var (Index.Pop index)) (indexIsoL lookup)

theorem indexIsoR (lookup : Lookup ts i t)
  : contextualise (HasType.Var lookup) = toCVar lookup := by
  rfl

def unembedTyped : CtxHasType ts e t -> HasType ts (unembed e) t
  | CtxHasType.CVar lookup => (unembedToCVar lookup).symm ▸ HasType.Var lookup
  | CtxHasType.CStar => HasType.Star
  | @CtxHasType.CLam ts a _ _ bodyTyped =>
      HasType.Lambda (unembedTyped (bodyTyped (@PTop ts a)))
  | CtxHasType.CApp e1 e2 => HasType.Apply (unembedTyped e1) (unembedTyped e2)

theorem isoL {h : HasType ts e t}
  : unembed (contextualise h) = e := by
  induction h with
  | Star => rfl
  | Apply e1 e2 ih1 ih2 => simp [contextualise, unembed, ih1, ih2]
  | Lambda e ih => simp [contextualise, unembed, ih]
  | Var i =>
      simp [contextualise, toCVar, fromVar, unembed]
      exact indexIsoL i

theorem isoL' {h : HasType ts e t}
  : unembed (contextualise h) = e := by
  induction h
    <;> simp [contextualise, unembed, *]
  case Var i =>
    simp [toCVar, fromVar, unembed]
    exact indexIsoL i

theorem isoR {ts : Ctx} {e : STLCCtx} {t : Ty}
  : (h : CtxHasType ts e t) -> contextualise (unembedTyped h) = e
  | CtxHasType.CVar lookup => by
      change contextualise ((unembedToCVar lookup).symm ▸ HasType.Var lookup) = toCVar lookup
      calc
        contextualise ((unembedToCVar lookup).symm ▸ HasType.Var lookup)
            = contextualise (HasType.Var lookup) := by
              have castContextualise {e1 e2 : STLC} (h : e1 = e2) (typed : HasType ts e1 t) :
                  contextualise (h ▸ typed) = contextualise typed := by
                cases h
                rfl
              exact castContextualise (unembedToCVar lookup).symm (HasType.Var lookup)
        _ = toCVar lookup := indexIsoR lookup
  | CtxHasType.CStar => rfl
  | @CtxHasType.CLam ts a _ _ bodyTyped => by
      simp [unembedTyped, contextualise, unembed]
      funext x
      cases x
      simp [isoR (bodyTyped (@PTop ts a))]
  | CtxHasType.CApp e1 e2 => by
      simp [unembedTyped, contextualise, isoR e1, isoR e2]

theorem isoR' {h : CtxHasType ts e t}
  : contextualise (unembedTyped h) = e := isoR h

-- Examples
------------

def showSTLCCtx : STLCCtx -> String
  | @STLCCtx.CVar _ ts' inst proxy => "CVar " ++ reprStr proxy ++ "[reified = " ++ reprStr (ReifyIndex.reify ts' (self := inst) proxy) ++ "]"
  | STLCCtx.CStar => "CStar"
  | @STLCCtx.CLam ts a body => "CLam (\\<ProxyTop> -> " ++ showSTLCCtx (body (@PTop ts a)) ++ ")"
  | STLCCtx.CApp f x => "CApp (" ++ showSTLCCtx f ++ ") (" ++ showSTLCCtx x ++ ")"

def idSTLC {ts : Ctx} {a : Ty} : STLCCtx :=
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
#eval showSTLCCtx (contextualise (unembedTyped idSTLCTyped'))
#eval unembed (contextualise (unembedTyped idSTLCTyped'))

def const {ts : Ctx} {a b : Ty} : STLCCtx :=
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
#eval showSTLCCtx (contextualise (unembedTyped constTyped'))
#eval unembed (contextualise (unembedTyped constTyped'))

def flipConst {ts : Ctx} {a b : Ty} : STLCCtx :=
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
#eval showSTLCCtx (contextualise (unembedTyped flipConstTyped'))
#eval unembed (contextualise (unembedTyped flipConstTyped'))

def const5 {ts : Ctx} {a b c d e : Ty} : STLCCtx :=
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
#eval showSTLCCtx (contextualise (unembedTyped const5Typed'))
#eval unembed (contextualise (unembedTyped const5Typed'))


-- Examples in theorems
------------------------

example {ts : Ctx} {a : Ty}
  : @STLCCtx.CLam ts a (fun x => STLCCtx.CVar (ts' := ts :/: a) x) =
    @STLCCtx.CLam ts a (fun y => STLCCtx.CVar (ts' := ts :/: a) y) := by
  rfl

example {ts : Ctx} {a : Ty}
  : @contextualise ts (STLC.Lambda a (STLC.Var Index.Top)) (a :-> a)
    (@HasType.Lambda ts a (STLC.Var Index.Top) a
      (@HasType.Var (ts :/: a) Index.Top a (@Lookup.Top ts a))) =
    @STLCCtx.CLam ts a (fun y => STLCCtx.CVar (ts' := ts :/: a) y) := by
  simp [contextualise, toCVar, fromIndex, fromVar]
  funext x
  cases x
  rfl

end ContextualEmbedding.Extrinsic.CE
