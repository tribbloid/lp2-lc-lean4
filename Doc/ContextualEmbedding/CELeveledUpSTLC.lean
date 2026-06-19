inductive Ty : Type
  | Unit : Ty
  | Fun : Ty -> Ty -> Ty
deriving Repr, DecidableEq
open Ty

-- https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Custom-Operators/
infixr:90 " :-> " => Fun

inductive Ctx : Type
  | Empty : Ctx
  | Snoc  : Ctx -> Ty -> Ctx
deriving Repr, DecidableEq

infixl:90 " :/: " => Ctx.Snoc

open Nat

inductive Index : Nat -> Ctx -> Ty -> Type where
  | Top : Index (succ l) (ts :/: t) t
  | Pop : Index l ts t -> Index (succ l) (ts :/: t') t
deriving Repr, DecidableEq
open Index


inductive STLC : Nat -> Ctx -> Ty -> Type where
  | Var    : Index l ts t -> STLC l ts t
  | Star   : STLC l ts Unit
  | Lambda : STLC (succ l) (ts :/: t1) t2 -> STLC l ts (t1 :-> t2)
  | Apply  : STLC l ts (t1 :-> t2) -> STLC l ts t1 -> STLC l ts t2
deriving Repr, DecidableEq
open STLC


inductive ProxyTop : Nat -> Ty -> Type where
  | PTop {l : Nat} {t : Ty} : ProxyTop (succ l) t
deriving Repr, DecidableEq
open ProxyTop

class ReifyIndex (l l' : Nat) (ts : Ctx) (t : Ty) where
  reify : ProxyTop l t -> Index l' ts t
open ReifyIndex


instance instReifyIndexRefl : ReifyIndex l l (ts :/: t) t where
  reify
    | PTop => Top

instance instReifyIndexSnoc [instRec : ReifyIndex l l' ts t] : ReifyIndex l (succ l') (ts :/: t') t where
  reify := λp => Pop (reify p)

inductive STLCCtx : Nat -> Ctx -> Ty -> Type where
  | CVar [ReifyIndex l l' ts t] : ProxyTop l t -> STLCCtx l' ts t
  | CStar : STLCCtx l ts Unit
  | CLam : (ProxyTop (succ l) a -> STLCCtx (succ l) (ts :/: a) b) -> STLCCtx l ts (a :-> b)
  | CApp : STLCCtx l ts (a :-> b) -> STLCCtx l ts a -> STLCCtx l ts b
open STLCCtx


-- Unembed
-----------

def unembed : STLCCtx l ts t -> STLC l ts t
  | CStar      => Star
  | CVar i     => Var (reify i)
  | CLam e     => Lambda (unembed (e PTop))
  | CApp e1 e2 => Apply (unembed e1) (unembed e2)


-- Contextualise
-----------------

inductive ProxyVar l' ts t where
  | PVar [inst : ReifyIndex l l' ts t] : ProxyTop l t -> ProxyVar l' ts t
deriving Repr
open ProxyVar

def weakenPVar : ProxyVar l ts t -> ProxyVar (succ l) (ts :/: t') t
  | PVar i => PVar i

def varTop : ProxyVar (succ l) (ts :/: t) t := PVar (@PTop l t)

def fromVar : ProxyVar l ts' t -> STLCCtx l ts' t
  | PVar i => CVar i

def fromIndex : Index l ts t -> ProxyVar l ts t
  | Top   => varTop
  | Pop i => weakenPVar (fromIndex i)

def toCVar : Index l ts t -> STLCCtx l ts t
  := λi => fromVar (fromIndex i)

def contextualise : STLC l ts t -> STLCCtx l ts t
  | Var i => toCVar i
  | (Lambda e) => CLam (λ_ => contextualise e)
  | (Apply e1 e2) => CApp (contextualise e1) (contextualise e2)
  | Star => CStar

--------------------------------------------
--           Isomorphism proofs           --
--------------------------------------------

/-
`STLC` and `STLCCtx` correspond very closely, so induction and simplification/rewriting takes care of a large chunk of the proof. The real meat of the issue is the isomorphism between `Index` and `ProxyTop` + `ReifyIndex`. Once we have that, the rest follows without much trouble.
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

Thankfully, we can use lean's field index notation. `(fromIndex i).2` means 'get the 2nd field of the return value of `fromIndex i`', which is the `ReifyIndex` instance. `(fromIndex i).3` is the `ProxyTop`.
-/
theorem indexIsoL (i : Index l ts' t)
  : reify (self := (fromIndex i).2) (fromIndex i).3 = i := by
  induction i with
  | Top => rfl
  | Pop i' ih => simp [fromIndex, weakenPVar, reify]
                 exact ih

--  fromIndex ∘ reify  --
--------------------------

/-
Now for the more difficult direction.

We no longer have a concrete index to form an induction on. We have only a `ProxyTop` and a `ReifyIndex` instance. In practice, the instance (and therefore the index) is determined by the levels, so you would hope that we could do some kind of induction on them, but sadly this won't help us.

If we know the levels we can *find* an instance, but that doesn't mean it's the same as the instance we've been given. Technically, type classes are open world in Haskell, Lean, and Agda, which means if we are given e.g. a `ReifyIndex l l ts t` instance, we can't say for certain that it's specifically the Refl instance (even though it will be in practice) because another overlapping instance for that type could be defined elsewhere.

Therefore, we need a 'closed world' axiom which says 'if you give me a `ReifyIndex` instance, it must either be `instReifyIndexRefl` or `instReifyIndexSnoc`'. We believe this is a reasonable assertion to make in practice since we can hide the type class from users by not exporting it.

-/

axiom closedWorld {l l' : Nat} {ts : Ctx} {t : Ty} (inst : ReifyIndex l l' ts t)
    -- Option 1: `inst` is the Refl instance, meaning the levels are the same, i.e. `l = l'`,
    --           and the context `ts` has a `t` at the top, i.e. `ts = ts' :/: t` for some `ts'`.

    --           `hEqL ▸ hEqTs ▸ inst` substitutes `l` for `l'` and `ts` for `ts' :/: t` in `inst`,
    --           otherwise the equality with
    --              `instReifyIndexRefl {l : Nat} {ts : Ctx} {t : Ty} : ReifyIndex l l (ts :/: t) t`
    --           would fail to type check.

    --           See: https://docs.lean-lang.org/theorem_proving_in_lean4/find/?domain=Verso.Genre.Manual.section&name=equality
  : (∃(ts' : Ctx) (hEqL : l = l') (hEqTs : ts = ts' :/: t), hEqL ▸ hEqTs ▸ inst = instReifyIndexRefl)
    \/
    -- Option 2: `inst` is the Snoc instance, meaning `l' = succ l''` for some `l''`,
    --           `ts = ts' :/: t'` for some `ts'` and `t'`,
    --           and there must be another `ReifyIndex` instance for that `l''`.

    --           The `:=` notation passes a value to a named implicit variable.
    --           See: https://lean-lang.org/lean4/doc/lean3changes.html?highlight=named%20implicit%20arguments#function-applications
    (∃(l'' : Nat) (ts' : Ctx) (t' : Ty) (hEqL : l' = succ l'') (hEqTs : ts = ts' :/: t') (inst' : ReifyIndex l l'' ts' t),
       hEqL ▸ hEqTs ▸ inst = instReifyIndexSnoc (instRec := inst'))

/-
The `indexIsoR` lemma says that `fromIndex` is the inverse of `reify`.

Here we need to use our `closedWorld` axiom to perform a case analysis on the `ReifyIndex` instance.
-/

theorem indexIsoR (inst : ReifyIndex l l' ts t) (i : ProxyTop l t):
  (fromIndex (reify (self := inst) i))
    = PVar (inst := inst) i
  := Or.elim (closedWorld inst)
        -- Option 1: `inst` is the Refl instance, corresponding to `Top`
        (λ⟨ts', hEqL, hEqTs, instEqRefl⟩ -- We use `⟨ ⟩` brackets as syntactic sugar for existential elimination
                        -- See: https://docs.lean-lang.org/theorem_proving_in_lean4/find/?domain=Verso.Genre.Manual.section&name=the-existential-quantifier
            => by subst hEqL hEqTs   -- `hEqL` tells us `l = l'` and `hEqTs` tells us `ts = ts' :/: t`,
                                     -- so we do this substitution everywhere using `subst`
                  simp at instEqRefl -- Simplify `instEqRefl` to get the two '▸' out of the way
                  rw [instEqRefl]    -- Rewrite `inst` with the Refl instance
                  cases i            -- Only one case, `PTop`, but we need it to be concrete
                                     -- so the LHS of the goal can be evaluated by `rfl`
                  rfl
        )
        -- Option 2: `inst` is the Snoc instance, corresponding to `Pop`
        (λ⟨l'', ts', t', hEqL, hEqTs, inst', instEqSnoc⟩
            => by subst hEqL hEqTs
                  simp at instEqSnoc                  -- Same idea as the Refl case
                  simp [instEqSnoc, reify, fromIndex] -- Simplify and rewrite using these equalities and function definitions
                  rw [indexIsoR]                      -- Recursive/inductive step
                  rfl
        )


-------------------------------
--      STLC Isomorphism     --
-------------------------------

/-
With the index isomorphisms out of the way, the isomorphism proofs for `STLC` and `STLCCtx` are almost entirely taken care of by inducting on the term, simplifying with function definitions and the inductive hypotheses, and reflexivity (with normalisation). The only slightly more interesting cases are:

* In `isoL`, `Var` uses the `indexIsoL` isomorphism.
* In `isoR`, `CVar` uses the `indexIsoR` isomorphism and `CLam` uses function extensionality.
-/

-- unembed ∘ contextualise
----------------------------

theorem isoL {l : Nat} {ts : Ctx} {t : Ty} {e : STLC l ts t}
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

theorem isoR {l : Nat} {ts : Ctx} {t : Ty} {e : STLCCtx l ts t}
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

def showSTLCCtx : STLCCtx l ts t -> String
  | CVar i => "CVar " ++ reprStr i ++ "[reifyd = " ++ reprStr (reify i : Index l ts t) ++ "]"
  | CStar  => "CStar"
  | CLam f => "CLam (\\<ProxyTop> -> " ++ showSTLCCtx (f PTop) ++ ")"
  | CApp f x => "CApp (" ++ showSTLCCtx f ++ ") (" ++ showSTLCCtx x ++ ")"


def idSTLC : STLCCtx l ts (a :-> a)
  := CLam (λx => CVar x)
def idSTLC' := @idSTLC zero Ctx.Empty Unit

#check idSTLC
#eval showSTLCCtx idSTLC'
#eval unembed idSTLC'
#eval (showSTLCCtx ∘ contextualise ∘ unembed) idSTLC'
#eval (unembed ∘ contextualise ∘ unembed) idSTLC'


def const : STLCCtx l ts (a :-> b :-> a)
  := CLam (λx => CLam (λ_y => CVar x))
def const' := @const zero Ctx.Empty Unit Unit

#eval showSTLCCtx const'
#eval unembed const'
#eval (showSTLCCtx ∘ contextualise ∘ unembed) const'
#eval (unembed ∘ contextualise ∘ unembed) const'

def flipConst : STLCCtx l ts (a :-> b :-> b)
  := CLam (λ_x => CLam (λy => CVar y))
def flipConst' := @flipConst zero Ctx.Empty Unit Unit

#check flipConst
#eval showSTLCCtx flipConst'
#eval unembed flipConst'
#eval (showSTLCCtx ∘ contextualise ∘ unembed) flipConst'
#eval (unembed ∘ contextualise ∘ unembed) flipConst'


-- def const5 : STLCCtx l ts (a :-> b :-> c :-> d :-> e :-> a)
--   := CLam (λx1 => CLam (λ_x2 => CLam (λ_x3 => CLam (λ_x4 => CLam (λ_x5 => CVar x1)))))
-- def const5' := @const5 zero Ctx.Empty Unit Unit Unit Unit Unit

-- #eval showSTLCCtx const5'
-- #eval unembed const5'
-- #eval (showSTLCCtx ∘ contextualise ∘ unembed) const5'
-- #eval (unembed ∘ contextualise ∘ unembed) const5'


-- Examples in theorems
------------------------

example {ts : Ctx} {a : Ty}
  : @CLam l a ts a (λx => CVar x) =  @CLam l a ts a (λy => CVar y) := by
  rfl

example {ts : Ctx} {a : Ty}
  : contextualise (Lambda (Var Top)) = @CLam l a ts a (λy => CVar y) := by
  simp [contextualise, toCVar, fromIndex, fromVar]
  funext x
  cases x
  rfl
