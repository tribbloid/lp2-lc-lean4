namespace ContextualEmbedding.CE

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

inductive Index : Ctx -> Ty -> Type where
  | Top {ts : Ctx} {t : Ty} : Index (ts :/: t) t
  | Pop {ts : Ctx} {t t' : Ty} : Index ts t -> Index (ts :/: t') t
deriving Repr, DecidableEq
open Index


inductive STLC : Ctx -> Ty -> Type where
  | Var    : Index ts t -> STLC ts t
  | Star   : STLC ts Unit
  | Lambda : STLC (ts :/: t1) t2 -> STLC ts (t1 :-> t2)
  | Apply  : STLC ts (t1 :-> t2) -> STLC ts t1 -> STLC ts t2
deriving Repr, DecidableEq
open STLC


inductive ProxyTop : Ctx -> Ty -> Type where
  | PTop {ts : Ctx} {t : Ty} : ProxyTop (ts :/: t) t
deriving Repr, DecidableEq
open ProxyTop

class ReifyIndex (ts : Ctx) (ts' : Ctx) where
  reify : ProxyTop ts t -> Index ts' t
open ReifyIndex

instance instReifyIndexRefl : ReifyIndex ts ts where
  reify
    | PTop => Top

instance instReifyIndexSnoc [instRec : ReifyIndex ts1 ts2] : ReifyIndex ts1 (ts2 :/: t) where
  reify := λp => Pop (reify p)

inductive STLCCtx : Ctx -> Ty -> Type where
  | CVar [ReifyIndex ts ts'] : ProxyTop ts t -> STLCCtx ts' t
  | CStar : STLCCtx ts Unit
  | CLam : (ProxyTop (ts :/: a) a -> STLCCtx (ts :/: a) b) -> STLCCtx ts (a :-> b)
  | CApp : STLCCtx ts (a :-> b) -> STLCCtx ts a -> STLCCtx ts b
open STLCCtx


-- Unembed
-----------

def unembed : STLCCtx ts t -> STLC ts t
  | CStar      => Star
  | CVar i     => Var (reify i)
  | CLam e     => Lambda (unembed (e PTop))
  | CApp e1 e2 => Apply (unembed e1) (unembed e2)


-- Contextualise
-----------------

inductive ProxyVar ts' t where
  | PVar [inst : ReifyIndex ts ts'] : ProxyTop ts t -> ProxyVar ts' t
deriving Repr
open ProxyVar

def weakenPVar : ProxyVar ts' t -> ProxyVar (ts' :/: t') t
  | PVar i => PVar i

def varTop : ProxyVar (ts :/: t) t := PVar (@PTop ts t)

def fromVar : ProxyVar ts' t -> STLCCtx ts' t
  | PVar i => CVar i

def fromIndex : Index ts t -> ProxyVar ts t
  | Top   => varTop
  | Pop i => weakenPVar (fromIndex i)

def toCVar : Index ts t -> STLCCtx ts t
  := λi => fromVar (fromIndex i)

def contextualise : STLC ts t -> STLCCtx ts t
  | Var i => toCVar i
  | Lambda e => CLam (λ_ => contextualise e)
  | Apply e1 e2 => CApp (contextualise e1) (contextualise e2)
  | Star => CStar

--------------------------------------------
--           Isomorphism proofs           --
--------------------------------------------

/-
`STLC` and `STLCCtx` correspond very closely, so induction and
simplification/rewriting takes care of a large chunk of the proof. The real meat
of the issue is the isomorphism between `Index` and `ProxyTop` + `ReifyIndex`.
Once we have that, the rest follows without much trouble.
-/

-----------------------------
--    Index Isomorphism    --
-----------------------------

--  reify ∘ fromIndex  --
--------------------------

/--
We start from the easier direction, where we begin and end with `Index`:

The `indexIsoL` lemma says that `reify` is the inverse of `fromIndex`. The proof
itself is a relatively straightforward induction on the index. The intuition is
that for every `Pop` in the index, `fromIndex` weakens the `ProxyTop` by one,
which `reify` then turns back into a `Pop`.

The tricky part is that this `ProxyTop` and the `ReifyIndex` instance we need
for `reify` are existential within the `ProxyVar` returned by `fromIndex`, which
makes them awkward refer to in the type of this lemma.

Thankfully, we can use lean's field index notation. `(fromIndex i).2` means 'get
the 2nd field of the return value of `fromIndex i`', which is the `ReifyIndex`
instance. `(fromIndex i).3` is the `ProxyTop`.
-/
theorem indexIsoL (i : Index ts' t)
  : reify (self := (fromIndex i).2) (fromIndex i).3 = i := by
  induction i with
  | Top => rfl
  | Pop i' ih =>
      change Pop (reify (self := (fromIndex i').2) (fromIndex i').3) = Pop i'
      exact congrArg Pop ih


--  fromIndex ∘ reify  --
--------------------------

/--
Now for the more difficult direction.

We no longer have a concrete index to form an induction on. We have only a
`ProxyTop` and a `ReifyIndex` instance. In practice, the instance (and therefore
the index) is determined by the contexts, so you would hope that we could do
some kind of induction on them, but sadly this won't help us.

If we know the contexts we can *find* an instance, but that doesn't mean it's
the same as the instance we've been given. Technically, type classes are open
world in Haskell, Lean, and Agda, which means if we are given e.g. a `ReifyIndex
ts ts` instance, we can't say for certain that it's specifically the Refl
instance (even though it will be in practice) because another overlapping
instance for that type could be defined elsewhere.

Therefore, we need a 'closed world' axiom which says 'if you give me a
`ReifyIndex` instance, it must either be `instReifyIndexRefl` or
`instReifyIndexSnoc`'. We believe this is a reasonable assertion to make in
practice since we can hide the type class from users by not exporting it.

-/
axiom closedWorld {ts1 ts2 : Ctx} (inst : ReifyIndex ts1 ts2)
    -- Option 1: `inst` is the Refl instance and the contexts are the same, i.e. `ts1 = ts2`.
    --           `hEq ▸ inst` substitutes `ts1` for `ts2` in `inst`, otherwise the equality with
    --           `instReifyIndexRefl {ts : Ctx} : ReifyIndex ts ts` would fail to type check.
    --           See: https://docs.lean-lang.org/theorem_proving_in_lean4/find/?domain=Verso.Genre.Manual.section&name=equality
  : (∃(hEq : ts1 = ts2), hEq ▸ inst = instReifyIndexRefl)
    \/
    -- Option 2: `inst` is the Snoc instance, `ts2` must be `ts2' :/: t` for some `ts2'` and some `t`,
    --           and there must be another `ReifyIndex` instance for that `ts2'`.
    --           The `:=` notation passes a value to a named implicit variable.
    --           See: https://lean-lang.org/lean4/doc/lean3changes.html?highlight=named%20implicit%20arguments#function-applications
    (∃(ts2' : Ctx) (t : Ty) (hEq : ts2 = ts2' :/: t) (inst' : ReifyIndex ts1 ts2'),
       hEq ▸ inst = instReifyIndexSnoc (instRec := inst'))

/-
The `indexIsoR` lemma says that `fromIndex` is the inverse of `reify`.

Here we need to use our `closedWorld` axiom to perform a case analysis on the `ReifyIndex` instance.
-/

theorem indexIsoR (inst : ReifyIndex ts ts') (i : ProxyTop ts t):
  (fromIndex (reify (self := inst) i))
    = PVar (inst := inst) i
  := Or.elim (closedWorld inst)
        -- Option 1: `inst` is the Refl instance, corresponding to `Top`
        (λ⟨hEq, instEqRefl⟩ -- We use `⟨ ⟩` brackets as syntactic sugar for existential elimination
                        -- See: https://docs.lean-lang.org/theorem_proving_in_lean4/find/?domain=Verso.Genre.Manual.section&name=the-existential-quantifier
            => by subst hEq          -- `hEq` tells us `ts = ts'`, so we do this substitution everywhere
                  simp at instEqRefl -- Simplify `instEqRefl` to get the '▸' out of the way
                  rw [instEqRefl]    -- Rewrite `inst` with the Refl instance
                  cases i            -- Only one case, `PTop`, but we need it to be concrete
                                     -- so the LHS of the goal can be evaluated by `rfl`
                  rfl
        )
        -- Option 2: `inst` is the Snoc instance, corresponding to `Pop`
        (λ⟨ts2', t', hEq, inst', instEqSnoc⟩
            => by subst hEq
                  simp at instEqSnoc                  -- Same idea as the Refl case
                  rw [instEqSnoc]
                  change weakenPVar (fromIndex (reify (self := inst') i))
                    = weakenPVar (PVar (inst := inst') i)
                  rw [indexIsoR inst' i]              -- Recursive/inductive step
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

theorem isoL {ts : Ctx} {t : Ty} {e : STLC ts t}
  : unembed (contextualise e) = e := by
  induction e with
  | Star => rfl
  | Apply e1 e2 ih1 ih2 => simp [contextualise, unembed, ih1, ih2]
  | Lambda f ih => simp [contextualise, unembed, ih]
  | Var i => simp [contextualise, toCVar, fromVar, unembed, indexIsoL]

-- More concise and reusable version:
theorem isoL' {ts : Ctx} {t : Ty} {e : STLC ts t}
  : unembed (contextualise e) = e := by
  induction e
    -- for each subgoal (`<;>`) introduced by the induction,
    -- try to satisfy the goal by simplifying with
    -- contextualise, unembed, and the local inductive hypotheses
    -- for each case (introduced by `*`)
    -- See: https://lean-lang.org/theorem_proving_in_lean4/Tactics/#Theorem-Proving-in-Lean-4--Tactics
    <;> simp [contextualise, unembed, *]

  -- Finish remaining Var case using index isomorphism
  case Var => simp [toCVar, fromVar, unembed, indexIsoL]

-- contextualise ∘ unembed
----------------------------

theorem isoR {ts : Ctx} {t : Ty} {e : STLCCtx ts t}
  : contextualise (unembed e) = e := by
  induction e with
  | CStar => rfl
  | CApp e1 e2 ih1 ih2 => simp [unembed, contextualise, ih1, ih2]
  | CVar => simp [unembed, contextualise, toCVar, indexIsoR]
            rfl
  | CLam f ih => simp [unembed, contextualise]
                 funext x
                 simp [ih]
                 cases x
                 rfl

-- More reusable:
theorem isoR' {ts : Ctx} {t : Ty} {e : STLCCtx ts t}
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
  case CVar => simp [toCVar, indexIsoR]
               rfl

-- Examples
------------

def showSTLCCtx : STLCCtx ts t -> String
  | CVar i => "CVar " ++ reprStr i ++ "[reified = " ++ reprStr (reify i : Index ts t) ++ "]"
  | CStar  => "CStar"
  | CLam f => "CLam (\\<ProxyTop> -> " ++ showSTLCCtx (f PTop) ++ ")"
  | CApp f x => "CApp (" ++ showSTLCCtx f ++ ") (" ++ showSTLCCtx x ++ ")"


def idSTLC : STLCCtx ts (a :-> a)
  := CLam (λx => CVar x)
def idSTLC' := @idSTLC Ctx.Empty Unit

#check idSTLC
#eval showSTLCCtx idSTLC'
#eval unembed idSTLC'
#eval (showSTLCCtx ∘ contextualise ∘ unembed) idSTLC'
#eval (unembed ∘ contextualise ∘ unembed) idSTLC'


def const : STLCCtx ts (a :-> b :-> a)
  := CLam (λx => CLam (λ_y => CVar x))
def const' := @const Ctx.Empty Unit Unit

#eval showSTLCCtx const'
#eval unembed const'
#eval (showSTLCCtx ∘ contextualise ∘ unembed) const'
#eval (unembed ∘ contextualise ∘ unembed) const'

def flipConst : STLCCtx ts (a :-> b :-> b)
  := CLam (λ_x => CLam (λy => CVar y))
def flipConst' := @flipConst Ctx.Empty Unit Unit

#check flipConst
#eval showSTLCCtx flipConst'
#eval unembed flipConst'
#eval (showSTLCCtx ∘ contextualise ∘ unembed) flipConst'
#eval (unembed ∘ contextualise ∘ unembed) flipConst'


def const5 : STLCCtx ts (a :-> b :-> c :-> d :-> e :-> a)
  := CLam (λx1 => CLam (λ_x2 => CLam (λ_x3 => CLam (λ_x4 => CLam (λ_x5 => CVar x1)))))
def const5' := @const5 Ctx.Empty Unit Unit Unit Unit Unit

#eval showSTLCCtx const5'
#eval unembed const5'
#eval (showSTLCCtx ∘ contextualise ∘ unembed) const5'
#eval (unembed ∘ contextualise ∘ unembed) const5'


-- Examples in theorems
------------------------

example {ts : Ctx} {a : Ty}
  : @CLam ts a a (λx => CVar x) =  @CLam ts a a (λy => CVar y) := by
  rfl

example {ts : Ctx} {a : Ty}
  : contextualise (Lambda (Var Top)) = @CLam ts a a (λy => CVar y) := by
  simp [contextualise, toCVar, fromIndex, fromVar]
  funext x
  cases x
  rfl

end ContextualEmbedding.CE
