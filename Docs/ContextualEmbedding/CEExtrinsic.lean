namespace ContextualEmbedding.CEExtrinsic

inductive Ty : Type
  | Unit : Ty
  | Fun : Ty -> Ty -> Ty
deriving Repr, DecidableEq
open Ty

infixr:90 " :-> " => Fun

inductive Ctx : Type
  | Empty : Ctx
  | Snoc  : Ctx -> Ty -> Ctx
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
  | Var    : Index -> STLC
  | Star   : STLC
  | Lambda : Ty -> STLC -> STLC
  | Apply  : STLC -> STLC -> STLC
deriving Repr, DecidableEq
open STLC

inductive HasType : Ctx -> STLC -> Ty -> Type where
  | Var    : Lookup ts i t -> HasType ts (Var i) t
  | Star   : HasType ts Star Unit
  | Lambda : HasType (ts :/: t1) e t2 -> HasType ts (Lambda t1 e) (t1 :-> t2)
  | Apply  : HasType ts e1 (t1 :-> t2) -> HasType ts e2 t1 -> HasType ts (Apply e1 e2) t2
deriving Repr

inductive ProxyTop : Ctx -> Ty -> Type where
  | PTop {ts : Ctx} {t : Ty} : ProxyTop (ts :/: t) t
deriving Repr, DecidableEq
open ProxyTop

inductive ReifyIndex : Ctx -> Ctx -> Ty -> Type where
  | Refl {ts : Ctx} {t : Ty} : ReifyIndex (ts :/: t) (ts :/: t) t
  | Snoc {ts1 ts2 : Ctx} {t t' : Ty} : ReifyIndex ts1 ts2 t -> ReifyIndex ts1 (ts2 :/: t') t
open ReifyIndex

attribute [class] ReifyIndex

instance instReifyIndexRefl : ReifyIndex (ts :/: t) (ts :/: t) t := Refl

instance instReifyIndexSnoc [instRec : ReifyIndex ts1 ts2 t] : ReifyIndex ts1 (ts2 :/: t') t :=
  Snoc instRec

def reifyWith : ReifyIndex ts ts' t -> ProxyTop ts t -> Index
  | Refl, PTop => Top
  | Snoc instRec, i => Pop (reifyWith instRec i)

def reify {ts ts' : Ctx} {t : Ty} [inst : ReifyIndex ts ts' t] : ProxyTop ts t -> Index :=
  reifyWith inst

def reifyLookupWith : (inst : ReifyIndex ts ts' t) -> (i : ProxyTop ts t) -> Lookup ts' (reifyWith inst i) t
  | Refl, PTop => Lookup.Top
  | Snoc instRec, i => Lookup.Pop (reifyLookupWith instRec i)

def reifyLookup {ts ts' : Ctx} {t : Ty} [inst : ReifyIndex ts ts' t] (i : ProxyTop ts t) :
    Lookup ts' (reify (inst := inst) i) t :=
  reifyLookupWith inst i

inductive STLCCtx : Ctx -> Ty -> Type where
  | CVar [inst : ReifyIndex ts ts' t] : ProxyTop ts t -> STLCCtx ts' t
  | CStar : STLCCtx ts Unit
  | CLam : (ProxyTop (ts :/: a) a -> STLCCtx (ts :/: a) b) -> STLCCtx ts (a :-> b)
  | CApp : STLCCtx ts (a :-> b) -> STLCCtx ts a -> STLCCtx ts b
open STLCCtx

def unembed : STLCCtx ts t -> STLC
  | CStar      => STLC.Star
  | @CVar _ _ _ inst i => STLC.Var (reifyWith inst i)
  | @CLam _ a _ e => STLC.Lambda a (unembed (e PTop))
  | CApp e1 e2 => STLC.Apply (unembed e1) (unembed e2)

def unembedTyped : (e : STLCCtx ts t) -> HasType ts (unembed e) t
  | CStar      => HasType.Star
  | @CVar _ _ _ inst i => HasType.Var (reifyLookupWith inst i)
  | CLam e     => HasType.Lambda (unembedTyped (e PTop))
  | CApp e1 e2 => HasType.Apply (unembedTyped e1) (unembedTyped e2)

inductive ProxyVar ts' t where
  | PVar [inst : ReifyIndex ts ts' t] : ProxyTop ts t -> ProxyVar ts' t
deriving Repr
open ProxyVar

def weakenPVar : ProxyVar ts' t -> ProxyVar (ts' :/: t') t
  | @PVar _ _ _ inst i => PVar (inst := Snoc inst) i

def varTop : ProxyVar (ts :/: t) t := PVar (inst := Refl) (@PTop ts t)

def fromVar : ProxyVar ts' t -> STLCCtx ts' t
  | @PVar _ _ _ inst i => CVar (inst := inst) i

def fromLookup : Lookup ts i t -> ProxyVar ts t
  | Lookup.Top   => varTop
  | Lookup.Pop h => weakenPVar (fromLookup h)

def toCVar : Lookup ts i t -> STLCCtx ts t :=
  fun i => fromVar (fromLookup i)

def contextualise : HasType ts e t -> STLCCtx ts t
  | HasType.Var i => toCVar i
  | HasType.Lambda e => CLam (fun _ => contextualise e)
  | HasType.Apply e1 e2 => CApp (contextualise e1) (contextualise e2)
  | HasType.Star => CStar

theorem indexIsoL (i : Lookup ts idx t)
  : reifyWith (fromLookup i).2 (fromLookup i).3 = idx := by
  induction i with
  | Top => rfl
  | Pop i' ih =>
      change Index.Pop (reifyWith (fromLookup i').2 (fromLookup i').3) = Index.Pop _
      exact congrArg Index.Pop ih

theorem indexIsoR (inst : ReifyIndex ts ts' t) (i : ProxyTop ts t) :
    fromLookup (reifyLookupWith inst i) = PVar (inst := inst) i := by
  induction inst with
  | Refl =>
      cases i
      rfl
  | Snoc instRec ih =>
      change weakenPVar (fromLookup (reifyLookupWith instRec i))
        = weakenPVar (PVar (inst := instRec) i)
      rw [ih]

theorem isoL {h : HasType ts e t}
  : unembed (contextualise h) = e := by
  induction h with
  | Star => rfl
  | Apply e1 e2 ih1 ih2 => simp [contextualise, unembed, ih1, ih2]
  | Lambda e ih => simp [contextualise, unembed, ih]
  | Var i => simp [contextualise, toCVar, fromVar, unembed, indexIsoL]

theorem isoL' {h : HasType ts e t}
  : unembed (contextualise h) = e := by
  induction h
    <;> simp [contextualise, unembed, *]
  case Var => simp [toCVar, fromVar, unembed, indexIsoL]

theorem isoR {e : STLCCtx ts t}
  : contextualise (unembedTyped e) = e := by
  induction e with
  | CStar => rfl
  | CApp e1 e2 ih1 ih2 => simp [unembedTyped, contextualise, ih1, ih2]
  | CVar => simp [unembedTyped, contextualise, toCVar, indexIsoR]
            rfl
  | CLam f ih =>
      simp [unembedTyped, contextualise, unembed]
      funext x
      simp [ih]
      cases x
      rfl

theorem isoR' {e : STLCCtx ts t}
  : contextualise (unembedTyped e) = e := by
  induction e
    <;> try (simp [unembedTyped, contextualise, unembed, *])
    <;> try (repeat' (funext p; cases p)
             <;> simp [*])
  case CVar => simp [toCVar, indexIsoR]
               rfl

def showSTLCCtx : STLCCtx ts t -> String
  | @CVar _ _ _ inst i => "CVar " ++ reprStr i ++ "[reified = " ++ reprStr (reifyWith inst i) ++ "]"
  | CStar  => "CStar"
  | CLam f => "CLam (\\<ProxyTop> -> " ++ showSTLCCtx (f PTop) ++ ")"
  | CApp f x => "CApp (" ++ showSTLCCtx f ++ ") (" ++ showSTLCCtx x ++ ")"

def idSTLC : STLCCtx ts (a :-> a)
  := CLam (fun x => CVar x)
def idSTLC' := @idSTLC Ctx.Empty Unit

#check idSTLC
#eval showSTLCCtx idSTLC'
#eval unembed idSTLC'
#eval showSTLCCtx (contextualise (unembedTyped idSTLC'))
#eval unembed (contextualise (unembedTyped idSTLC'))

def const : STLCCtx ts (a :-> b :-> a)
  := CLam (fun x => CLam (fun _ => CVar x))
def const' := @const Ctx.Empty Unit Unit

#eval showSTLCCtx const'
#eval unembed const'
#eval showSTLCCtx (contextualise (unembedTyped const'))
#eval unembed (contextualise (unembedTyped const'))

def flipConst : STLCCtx ts (a :-> b :-> b)
  := CLam (fun _ => CLam (fun y => CVar y))
def flipConst' := @flipConst Ctx.Empty Unit Unit

#check flipConst
#eval showSTLCCtx flipConst'
#eval unembed flipConst'
#eval showSTLCCtx (contextualise (unembedTyped flipConst'))
#eval unembed (contextualise (unembedTyped flipConst'))

def const5 : STLCCtx ts (a :-> b :-> c :-> d :-> e :-> a)
  := CLam (fun x1 => CLam (fun _ => CLam (fun _ => CLam (fun _ => CLam (fun _ => CVar x1)))))
def const5' := @const5 Ctx.Empty Unit Unit Unit Unit Unit

#eval showSTLCCtx const5'
#eval unembed const5'
#eval showSTLCCtx (contextualise (unembedTyped const5'))
#eval unembed (contextualise (unembedTyped const5'))

example {ts : Ctx} {a : Ty}
  : @CLam ts a a (fun x => CVar x) =  @CLam ts a a (fun y => CVar y) := by
  rfl

example {ts : Ctx} {a : Ty}
  : contextualise (HasType.Lambda (HasType.Var Lookup.Top)) = @CLam ts a a (fun y => CVar y) := by
  simp [contextualise, toCVar, fromLookup, fromVar]
  funext x
  cases x
  rfl

end ContextualEmbedding.CEExtrinsic
