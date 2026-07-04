namespace ContextualEmbedding.CEExtrinsic

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

def reifyLookupWith : (inst : ReifyIndex ts ts' t) -> (i : ProxyTop ts t) -> Lookup ts' (reifyWith inst i) t
  | Refl, PTop => Lookup.Top
  | Snoc instRec, i => Lookup.Pop (reifyLookupWith instRec i)

inductive STLCCtx : Type where
  | CVar {ts ts' : Ctx} {t : Ty} [inst : ReifyIndex ts ts' t] : ProxyTop ts t -> STLCCtx
  | CStar : STLCCtx
  | CLam {ts : Ctx} (a : Ty) : (ProxyTop (ts :/: a) a -> STLCCtx) -> STLCCtx
  | CApp : STLCCtx -> STLCCtx -> STLCCtx
open STLCCtx

inductive CtxHasType : Ctx -> STLCCtx -> Ty -> Type where
  | CVar {ts ts' : Ctx} {t : Ty} (inst : ReifyIndex ts ts' t) (i : ProxyTop ts t) :
      CtxHasType ts' (CVar (inst := inst) i) t
  | CStar : CtxHasType ts CStar Unit
  | CLam {ts : Ctx} {a b : Ty} {body : ProxyTop (ts :/: a) a -> STLCCtx} :
      ((i : ProxyTop (ts :/: a) a) -> CtxHasType (ts :/: a) (body i) b) ->
        CtxHasType ts (CLam a body) (a :-> b)
  | CApp : CtxHasType ts e1 (a :-> b) -> CtxHasType ts e2 a -> CtxHasType ts (CApp e1 e2) b

def unembed : STLCCtx -> STLC
  | CStar => STLC.Star
  | @CVar _ _ _ inst i => STLC.Var (reifyWith inst i)
  | @CLam _ a body => STLC.Lambda a (unembed (body PTop))
  | CApp e1 e2 => STLC.Apply (unembed e1) (unembed e2)

def unembedTyped : CtxHasType ts e t -> HasType ts (unembed e) t
  | CtxHasType.CStar => HasType.Star
  | @CtxHasType.CVar _ _ _ inst i => HasType.Var (reifyLookupWith inst i)
  | CtxHasType.CLam bodyTyped => HasType.Lambda (unembedTyped (bodyTyped PTop))
  | CtxHasType.CApp e1 e2 => HasType.Apply (unembedTyped e1) (unembedTyped e2)

inductive ProxyVar (ts' : Ctx) (t : Ty) where
  | PVar {ts : Ctx} [inst : ReifyIndex ts ts' t] : ProxyTop ts t -> ProxyVar ts' t
deriving Repr
open ProxyVar

def weakenPVar : ProxyVar ts' t -> ProxyVar (ts' :/: t') t
  | @PVar _ _ _ inst i => PVar (inst := Snoc inst) i

def varTop : ProxyVar (ts :/: t) t := PVar (inst := Refl) (@PTop ts t)

def fromVar : ProxyVar ts' t -> STLCCtx
  | @PVar _ _ _ inst i => CVar (inst := inst) i

def fromVarTyped : (v : ProxyVar ts t) -> CtxHasType ts (fromVar v) t
  | @PVar _ _ _ inst i => CtxHasType.CVar inst i

def fromLookup : Lookup ts i t -> ProxyVar ts t
  | Lookup.Top => varTop
  | Lookup.Pop h => weakenPVar (fromLookup h)

def contextualise : HasType ts e t -> STLCCtx
  | @HasType.Var _ _ _ h => fromVar (fromLookup h)
  | @HasType.Star _ => CStar
  | @HasType.Lambda ts t1 _ _ h => @CLam ts t1 (fun _ => contextualise h)
  | @HasType.Apply _ _ _ _ _ h1 h2 => CApp (contextualise h1) (contextualise h2)

def contextualiseTyped : (h : HasType ts e t) -> CtxHasType ts (contextualise h) t
  | @HasType.Var _ _ _ h => fromVarTyped (fromLookup h)
  | @HasType.Star _ => CtxHasType.CStar
  | @HasType.Lambda _ _ _ _ h => CtxHasType.CLam (fun _ => contextualiseTyped h)
  | @HasType.Apply _ _ _ _ _ h1 h2 => CtxHasType.CApp (contextualiseTyped h1) (contextualiseTyped h2)

theorem indexIsoL (i : Lookup ts idx t) :
    reifyWith (fromLookup i).2 (fromLookup i).3 = idx := by
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

theorem isoL {h : HasType ts e t} :
    unembed (contextualise h) = e := by
  induction h with
  | Star => rfl
  | Apply _ _ ih1 ih2 => simp [contextualise, unembed, ih1, ih2]
  | Lambda _ ih => simp [contextualise, unembed, ih]
  | Var i => simp [contextualise, fromVar, unembed, indexIsoL]

theorem isoL' {h : HasType ts e t} :
    unembed (contextualise h) = e := by
  induction h
    <;> simp [contextualise, unembed, *]
  case Var => simp [fromVar, unembed, indexIsoL]

theorem isoR {h : CtxHasType ts e t} :
    contextualise (unembedTyped h) = e := by
  induction h with
  | CStar => rfl
  | CApp _ _ ih1 ih2 => simp [unembedTyped, contextualise, ih1, ih2]
  | CVar inst i =>
      change fromVar (fromLookup (reifyLookupWith inst i)) = CVar (inst := inst) i
      rw [indexIsoR inst i]
      rfl
  | CLam bodyTyped ih =>
      simp [unembedTyped, contextualise, unembed]
      funext x
      cases x
      exact ih PTop

theorem isoR' {h : CtxHasType ts e t} :
    contextualise (unembedTyped h) = e := by
  induction h
    <;> try (simp [unembedTyped, contextualise, unembed, *])
    <;> try (repeat' (funext p; cases p)
             <;> simp [*])
  case CVar inst i =>
    change fromVar (fromLookup (reifyLookupWith inst i)) = CVar (inst := inst) i
    rw [indexIsoR inst i]
    rfl

def showSTLCCtx : STLCCtx -> String
  | @CVar _ _ _ inst i => "CVar " ++ reprStr i ++ "[reified = " ++ reprStr (reifyWith inst i) ++ "]"
  | CStar => "CStar"
  | @CLam _ _ body => "CLam (\\<ProxyTop> -> " ++ showSTLCCtx (body PTop) ++ ")"
  | CApp f x => "CApp (" ++ showSTLCCtx f ++ ") (" ++ showSTLCCtx x ++ ")"

def idSTLC (ts : Ctx) (a : Ty) : STLCCtx :=
  @CLam ts a (fun x => @CVar (ts :/: a) (ts :/: a) a Refl x)

def idSTLCTyped (ts : Ctx) (a : Ty) : CtxHasType ts (idSTLC ts a) (a :-> a) :=
  CtxHasType.CLam (fun x => CtxHasType.CVar Refl x)

def idSTLC' : STLCCtx := idSTLC Ctx.Empty Unit

def idSTLC'Typed : CtxHasType Ctx.Empty idSTLC' (Unit :-> Unit) :=
  idSTLCTyped Ctx.Empty Unit

#check idSTLC
#eval showSTLCCtx idSTLC'
#eval unembed idSTLC'
#eval showSTLCCtx (contextualise (unembedTyped idSTLC'Typed))
#eval unembed (contextualise (unembedTyped idSTLC'Typed))

def const (ts : Ctx) (a b : Ty) : STLCCtx :=
  @CLam ts a (fun x =>
    @CLam (ts :/: a) b (fun _ =>
      @CVar (ts :/: a) ((ts :/: a) :/: b) a (Snoc Refl) x))

def constTyped (ts : Ctx) (a b : Ty) : CtxHasType ts (const ts a b) (a :-> b :-> a) :=
  CtxHasType.CLam (fun x =>
    CtxHasType.CLam (fun _ =>
      CtxHasType.CVar (Snoc Refl) x))

def const' : STLCCtx := const Ctx.Empty Unit Unit

def const'Typed : CtxHasType Ctx.Empty const' (Unit :-> Unit :-> Unit) :=
  constTyped Ctx.Empty Unit Unit

#eval showSTLCCtx const'
#eval unembed const'
#eval showSTLCCtx (contextualise (unembedTyped const'Typed))
#eval unembed (contextualise (unembedTyped const'Typed))

def flipConst (ts : Ctx) (a b : Ty) : STLCCtx :=
  @CLam ts a (fun _ =>
    @CLam (ts :/: a) b (fun y =>
      @CVar ((ts :/: a) :/: b) ((ts :/: a) :/: b) b Refl y))

def flipConstTyped (ts : Ctx) (a b : Ty) : CtxHasType ts (flipConst ts a b) (a :-> b :-> b) :=
  CtxHasType.CLam (fun _ =>
    CtxHasType.CLam (fun y =>
      CtxHasType.CVar Refl y))

def flipConst' : STLCCtx := flipConst Ctx.Empty Unit Unit

def flipConst'Typed : CtxHasType Ctx.Empty flipConst' (Unit :-> Unit :-> Unit) :=
  flipConstTyped Ctx.Empty Unit Unit

#check flipConst
#eval showSTLCCtx flipConst'
#eval unembed flipConst'
#eval showSTLCCtx (contextualise (unembedTyped flipConst'Typed))
#eval unembed (contextualise (unembedTyped flipConst'Typed))

def const5 (ts : Ctx) (a b c d e : Ty) : STLCCtx :=
  @CLam ts a (fun x1 =>
    @CLam (ts :/: a) b (fun _ =>
      @CLam ((ts :/: a) :/: b) c (fun _ =>
        @CLam (((ts :/: a) :/: b) :/: c) d (fun _ =>
          @CLam ((((ts :/: a) :/: b) :/: c) :/: d) e (fun _ =>
            @CVar (ts :/: a) (((((ts :/: a) :/: b) :/: c) :/: d) :/: e) a (Snoc (Snoc (Snoc (Snoc Refl)))) x1)))))

def const5Typed (ts : Ctx) (a b c d e : Ty) : CtxHasType ts (const5 ts a b c d e) (a :-> b :-> c :-> d :-> e :-> a) :=
  CtxHasType.CLam (fun x1 =>
    CtxHasType.CLam (fun _ =>
      CtxHasType.CLam (fun _ =>
        CtxHasType.CLam (fun _ =>
          CtxHasType.CLam (fun _ =>
            CtxHasType.CVar (Snoc (Snoc (Snoc (Snoc Refl)))) x1)))))

def const5' : STLCCtx := const5 Ctx.Empty Unit Unit Unit Unit Unit

def const5'Typed : CtxHasType Ctx.Empty const5' (Unit :-> Unit :-> Unit :-> Unit :-> Unit :-> Unit) :=
  const5Typed Ctx.Empty Unit Unit Unit Unit Unit

#eval showSTLCCtx const5'
#eval unembed const5'
#eval showSTLCCtx (contextualise (unembedTyped const5'Typed))
#eval unembed (contextualise (unembedTyped const5'Typed))

example {ts : Ctx} {a : Ty} :
    idSTLC ts a = idSTLC ts a := by
  rfl

example {ts : Ctx} {a : Ty} :
    contextualise (@HasType.Lambda ts a (STLC.Var Index.Top) a
      (@HasType.Var (ts :/: a) Index.Top a (@Lookup.Top ts a))) = idSTLC ts a := by
  simp [contextualise, idSTLC, fromLookup, fromVar, varTop]
  funext x
  cases x
  rfl

end ContextualEmbedding.CEExtrinsic
