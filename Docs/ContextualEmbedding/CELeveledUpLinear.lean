inductive Ty : Type
  | Unit : Ty
  | Tensor : Ty -> Ty -> Ty
  | Fun : Ty -> Ty -> Ty
deriving Repr, DecidableEq
open Ty

-- https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Custom-Operators/
infixr:90 " :-* " => Fun
infixr:80 " :* " => Tensor

inductive CtxElem where
  | J : Ty -> CtxElem
  | N : CtxElem
deriving Repr, DecidableEq
open CtxElem

inductive Ctx : Type
  | Empty : Ctx
  | Snoc  : Ctx -> CtxElem -> Ctx
deriving Repr, DecidableEq

infixl:90 " :/: " => Ctx.Snoc

open Nat

inductive Index : Nat -> Ctx -> Ctx -> Ty -> Type where
  | Top : Index (succ l) (ts :/: J t) (ts :/: N) t
  | Pop : Index l ci co t -> Index (succ l) (ci :/: a) (co :/: a) t
deriving Repr, DecidableEq
open Index


inductive LLC : Nat -> Ctx -> Ctx -> Ty -> Type where
  | Var  : Index l ci co t -> LLC l ci co t
  | UnitT : LLC l ci ci Unit
  | Pair  : LLC l ci ctx t1 -> LLC l ctx co t2 -> LLC l ci co (t1 :* t2)
  | Letp  : LLC l ci ctx (t1 :* t2)
            -> LLC (succ (succ l)) (ctx :/: J t1 :/: J t2) (co :/: N :/: N) t
            -> LLC l ci co t
  | Lam   : LLC (succ l) (ci :/: J t1) (co :/: N) t2
            -> LLC l ci co (t1 :-* t2)
  | App   : LLC l ci ctx (t1 :-* t2) -> LLC l ctx co t1 -> LLC l ci co t2
deriving Repr, DecidableEq
open LLC


inductive ProxyTop : Nat -> CtxElem -> CtxElem -> Ty -> Type where
  | PTop : ProxyTop (succ l) (J t) N t
deriving Repr, DecidableEq
open ProxyTop

class ReifyIndex (l l' : Nat) (i o : CtxElem) (ci : Ctx) (co : outParam Ctx) (t : Ty) where
  reify : ProxyTop l i o t -> Index l' ci co t
open ReifyIndex

instance instReifyIndexRefl : ReifyIndex l l i o (zs :/: i) (zs :/: o) t where
  reify
    | PTop => Top

instance instReifyIndexSnoc [instRec : ReifyIndex l l' i o ci co t]
  : ReifyIndex l (succ l') i o (ci :/: z) (co :/: z) t where
  reify := λp => Pop (reify p)


inductive LLCCtx : Nat -> Ctx -> Ctx -> Ty -> Type where
  | CVar [ReifyIndex l l' i o ci co t] : ProxyTop l i o t -> LLCCtx l' ci co t
  | CUnitT : LLCCtx l ci ci Unit
  | CPair  : LLCCtx l ci ctx a -> LLCCtx l ctx co b -> LLCCtx l ci co (a :* b)
  | CLetp  : LLCCtx l ci ctx (a :* b)
            -> (ProxyTop (succ l) (J a) N a
                -> ProxyTop (succ (succ l)) (J b) N b
                -> LLCCtx (succ (succ l)) (ctx :/: J a :/: J b) (co :/: N :/: N) t)
            -> LLCCtx l ci co t
  | CLam : (ProxyTop (succ l) (J a) N a -> LLCCtx (succ l) (ci :/: J a) (co :/: N) b)
        -> LLCCtx l ci co (a :-* b)
  | CApp : LLCCtx l ci ctx (a :-* b) -> LLCCtx l ctx co a -> LLCCtx l ci co b
open LLCCtx


-- Unembed
-----------

def unembed : LLCCtx l ci co t -> LLC l ci co t
  | CUnitT     => UnitT
  | CVar i     => Var (reify i)
  | CPair x y  => Pair (unembed x) (unembed y)
  | CLetp x binders => Letp (unembed x)
                            (unembed (binders PTop PTop))
  | CLam e     => Lam (unembed (e PTop))
  | CApp e1 e2 => App (unembed e1) (unembed e2)


-- Contextualise
-----------------

inductive ProxyVar l' ci co t where
  | PVar [inst : ReifyIndex l l' i o ci co t] : ProxyTop l i o t -> ProxyVar l' ci co t
deriving Repr
open ProxyVar

def weakenPVar : ProxyVar l ci co t -> ProxyVar (succ l) (ci :/: x) (co :/: x) t
  | PVar i => PVar i

def varTop : ProxyVar (succ l) (ci :/: J t) (ci :/: N) t := PVar (@PTop l t)

def fromVar : ProxyVar l ci co t -> LLCCtx l ci co t
  | PVar i => CVar i

def fromIndex : Index l ci co t -> ProxyVar l ci co t
  | Top   => varTop
  | Pop i => weakenPVar (fromIndex i)

def toCVar : Index l ci co t -> LLCCtx l ci co t
  := λi => fromVar (fromIndex i)

def contextualise : LLC l ci co t -> LLCCtx l ci co t
  | Var i => toCVar i
  | Lam e => CLam (λ_ => contextualise e)
  | Pair x y  => CPair (contextualise x) (contextualise y)
  | Letp x binders => CLetp (contextualise x)
                            (λ_ _ => contextualise binders)
  | App e1 e2 => CApp (contextualise e1) (contextualise e2)
  | UnitT => CUnitT

--------------------------------------------
--           Isomorphism proofs           --
--------------------------------------------

/-
`LLC` and `LLCCtx` correspond very closely, so induction and simplification/rewriting takes care of a large chunk of the proof. The real meat of the issue is the isomorphism between `Index` and `ProxyTop` + `ReifyIndex`. Once we have that, the rest follows without much trouble.
-/

-----------------------------
--    Index Isomorphism    --
-----------------------------

--  reify ∘ fromIndex  --
--------------------------

/-
We start from the easier direction, where we begin and end with `Index`:

The `indexIsoL` lemma says that `reify` is the inverse of `fromIndex`. The proof itself is a relatively straightforward induction on the index. The intuition is that for every `Pop` in the index, `fromIndex` weakens the `ProxyTop` by one, which `reify` then turns back into a `Pop`.

The tricky part is that this `ProxyTop` and the `ReifyIndex` instance we need for `reify` are existential within the `ProxyVar` returned by `fromIndex`, which makes them awkward refer to in the type of this lemma.

Thankfully, we can use lean's field index notation. `(fromIndex i).4` means 'get the 4th field of the return value of `fromIndex i`', which is the `ReifyIndex` instance. `(fromIndex i).5` is the `ProxyTop`.
-/
theorem indexIsoL (i : Index l ci co t)
  : reify (self := (fromIndex i).4) (fromIndex i).5 = i := by
  induction i with
  | Top => rfl
  | Pop i' ih => simp [fromIndex, weakenPVar, reify]
                 exact ih

--  fromIndex ∘ reify  --
--------------------------

/-
Now for the more difficult direction.

We no longer have a concrete index to form an induction on. We have only a `ProxyTop` and a `ReifyIndex` instance. In practice, the instance (and therefore the index) is determined by the levels, so you would hope that we could do some kind of induction on them, but sadly this won't help us.

If we know the levels we can *find* an instance, but that doesn't mean it's the same as the instance we've been given. Technically, type classes are open world in Haskell, Lean, and Agda, which means if we are given e.g. a `ReifyIndex l l i o (ci :/: i) (co :/: o) t` instance, we can't say for certain that it's specifically the Refl instance (even though it will be in practice) because another overlapping instance for that type could be defined elsewhere.

Therefore, we need a 'closed world' axiom which says 'if you give me a `ReifyIndex` instance, it must either be `instReifyIndexRefl` or `instReifyIndexSnoc`'. We believe this is a reasonable assertion to make in practice since we can hide the type class from users by not exporting it.

-/

axiom closedWorld {l l' : Nat} {i o : CtxElem} {ci co : Ctx} {t : Ty} (inst : ReifyIndex l l' i o ci co t)
    -- Option 1: `inst` is the Refl instance, meaning the levels are the same, i.e. `l = l'`,
    --           and for some `ts` the input context `ci` must be `ts :/: i` and
    --           the output context `co` must be `ts :/: o`.

    --           `hEqL ▸ hEqCi ▸ hEqCo ▸ inst` substitutes `l` for `l'`, `ci` for `ts :/: i`,
    --           and `co` for `ts :/: o` in `inst`, otherwise the equality with
    --              `instReifyIndexRefl {l : Nat} {i o : CtxElem} {zs : Ctx} {t : Ty}
    --                 : ReifyIndex l l i o (zs :/: i) (zs :/: o) t`
    --           would fail to type check.

    --           See: https://docs.lean-lang.org/theorem_proving_in_lean4/find/?domain=Verso.Genre.Manual.section&name=equality
  : (∃(ts : Ctx) (hEqL : l = l') (hEqCi : ci = ts :/: i) (hEqCo : co = ts :/: o),
       hEqL ▸ hEqCi ▸ hEqCo ▸ inst = instReifyIndexRefl)
    \/
    -- Option 2: `inst` is the Snoc instance, meaning `l' = succ l''` for some `l''`,
    --           for some `z`, `ci'`, and `co'` the input context `ci` must be `ci' :/: z`
    --           and the output context `co` must be `co' :/: z`,
    --           and there must be another `ReifyIndex` instance for that `l''`.

    --           The `:=` notation passes a value to a named implicit variable.
    --           See: https://lean-lang.org/lean4/doc/lean3changes.html?highlight=named%20implicit%20arguments#function-applications
    (∃(l'' : Nat) (ci' co' : Ctx) (z : CtxElem)
      (hEqL : l' = succ l'') (hEqCi : ci = ci' :/: z) (hEqCo : co = co' :/: z)
      (inst' : ReifyIndex l l'' i o ci' co' t),
       hEqL ▸ hEqCi ▸ hEqCo ▸ inst = instReifyIndexSnoc (instRec := inst'))

/-
The `indexIsoR` lemma says that `fromIndex` is the inverse of `reify`.

Here we need to use our `closedWorld` axiom to perform a case analysis on the `ReifyIndex` instance.
-/

theorem indexIsoR (inst : ReifyIndex l l' i o ci co t) (pt : ProxyTop l i o t):
  (fromIndex (reify (self := inst) pt))
    = PVar (inst := inst) pt
  := Or.elim (closedWorld inst)
        -- Option 1: `inst` is the Refl instance, corresponding to `Top`
        (λ⟨ts, hEqL, hEqCi, hEqCo, instEqRefl⟩ -- We use `⟨ ⟩` brackets as syntactic sugar for existential elimination
                        -- See: https://docs.lean-lang.org/theorem_proving_in_lean4/find/?domain=Verso.Genre.Manual.section&name=the-existential-quantifier
            => by subst hEqL hEqCi hEqCo -- `hEqL` tells us `l = l'`,
                                         -- `hEqCi` tells us `ci = ts :/: i`, and
                                         -- `hEqCo` tells us `co = ts :/: o`,
                                         -- so we do this substitution everywhere using `subst`.
                  simp at instEqRefl     -- Simplify `instEqRefl` to get the two '▸' out of the way
                  rw [instEqRefl]        -- Rewrite `inst` with the Refl instance
                  cases pt               -- Only one case, `PTop`, but we need it to be concrete
                                         -- so the LHS of the goal can be evaluated by `rfl`
                  rfl
        )
        -- Option 2: `inst` is the Snoc instance, corresponding to `Pop`
        (λ⟨l'', ci', co', z, hEqL, hEqCi, hEqCo, inst', instEqSnoc⟩
            => by subst hEqL hEqCi hEqCo
                  simp at instEqSnoc                  -- Same idea as the Refl case
                  simp [instEqSnoc, reify, fromIndex] -- Simplify and rewrite using these equalities and function definitions
                  rw [indexIsoR]                      -- Recursive/inductive step
                  rfl
        )

-------------------------------
--      LLC Isomorphism      --
-------------------------------

/-
With the index isomorphisms out of the way, the isomorphism proofs for `LLC` and `LLCCtx` are almost entirely taken care of by inducting on the term, simplifying with function definitions and the inductive hypotheses, and reflexivity (with normalisation). The only slightly more interesting cases are:

* In `isoL`, `Var` uses the `indexIsoL` isomorphism.
* In `isoR`, `CVar` uses the `indexIsoR` isomorphism and `CLam` uses function extensionality.
-/

-- unembed ∘ contextualise
----------------------------

theorem isoL {l : Nat} {ci co : Ctx} {t : Ty} {e : LLC l ci co t}
  : unembed (contextualise e) = e := by
  induction e
    -- for each subgoal (`<;>`) introduced by the induction,
    -- try to satisfy the goal by simplifying with
    -- contextualise, unembed, and the local inductive hypotheses
    -- for each case (introduced by `*`)
    -- See: https://lean-lang.org/theorem_proving_in_lean4/Tactics/#Theorem-Proving-in-Lean-4--Tactics
    <;> simp [contextualise, unembed, *]

  -- Finish remaining Var case using index isomorphism
  case Var i => simp [contextualise, toCVar, fromVar, unembed, indexIsoL]

-- contextualise ∘ unembed
----------------------------

theorem isoR {l : Nat} {ci co : Ctx} {t : Ty} {e : LLCCtx l ci co t}
  : contextualise (unembed e) = e := by
  induction e
    -- Start by simplifying all cases with contextualise, unembed, and local hypotheses.
    -- This covers any cases which don't involve binders.
    <;> try (simp [contextualise, unembed, *])
    -- For any cases which involve introducing binders,
    -- repeatedly apply function extensionality and case analysis on the introduced variable,
    -- until all binders accounted for.
    -- Then simplify.
    <;> try (repeat' (funext p; cases p)
             <;> simp [*])
  -- Deal with leftover CVar case using index isomorphism
  case CVar => simp [unembed, contextualise, toCVar, indexIsoR]
               rfl

-- Examples
------------

def showLLCCtx : LLCCtx l ci co t -> String
  | CVar i => "CVar " ++ reprStr i ++ "[reifyd = " ++ reprStr (reify i : Index l ci co t) ++ "]"
  | CUnitT  => "CUnitT"
  | CLam f => "CLam (λ<PTop> -> " ++ showLLCCtx (f PTop) ++ ")"
  | CApp f x => "CApp (" ++ showLLCCtx f ++ ") (" ++ showLLCCtx x ++ ")"
  | CPair x y  => "CPair (" ++ showLLCCtx x ++ ") (" ++ showLLCCtx y ++ ")"
  | CLetp x binders => "CLetp (" ++ showLLCCtx x ++ ") (λ<PTop> <PTop> -> " ++ showLLCCtx (binders PTop PTop) ++ ")"


def idLLC : LLCCtx l ci ci (a :-* a)
  := CLam (λx => CVar x)
def idLLC' := @idLLC zero Ctx.Empty Unit

#check idLLC
#eval showLLCCtx idLLC'
#eval unembed idLLC'
#eval (showLLCCtx ∘ contextualise ∘ unembed) idLLC'
#eval (unembed ∘ contextualise ∘ unembed) idLLC'


-- Non-linear! Should fail
-- def const : LLCCtx l ci ci (a :-* b :-* a)
--   := CLam (λx => CLam (λ_y => CVar x))
-- def const' := @const zero Ctx.Empty Unit Unit


-- Non-linear! Should fail
-- def flipConst : LLCCtx l ci ci (a :-* b :-* b)
--   := CLam (λ_x => CLam (λy => CVar y))
-- def flipConst' := @flipConst zero Ctx.Empty Unit Unit

-- Non-linear! Should fail
-- def const5 : LLCCtx l ci co (a :-* b :-* c :-* d :-* e :-* a)
--   := CLam (λx1 => CLam (λ_x2 => CLam (λ_x3 => CLam (λ_x4 => CLam (λ_x5 => CVar x1)))))
-- def const5' := @const5 zero Ctx.Empty Unit Unit Unit Unit Unit


def pair : LLCCtx l ci ci (a :-* b :-* (a :* b))
  := CLam (λx => CLam (λy => CPair (CVar x) (CVar y)))
def pair' := @pair zero Ctx.Empty Unit Unit


#eval showLLCCtx pair'
#eval unembed pair'
#eval (showLLCCtx ∘ contextualise ∘ unembed) pair'
#eval (unembed ∘ contextualise ∘ unembed) pair'
