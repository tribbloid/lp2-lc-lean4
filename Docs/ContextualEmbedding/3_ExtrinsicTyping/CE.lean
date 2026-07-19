namespace ContextualEmbedding.ExtrinsicTyping.CE

inductive Ty : Type
  | Unit : Ty
  | Fun : Ty -> Ty -> Ty
deriving Repr, DecidableEq
open Ty

-- https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Custom-Operators/
infixr:90 " :-> " => Fun

abbrev Ctx : Type := Nat

inductive Index : Ctx -> Type where
  | Top {ts : Ctx} : Index (ts + 1)
  | Pop {ts : Ctx} : Index ts -> Index (ts + 1)
deriving Repr, DecidableEq
open Index

inductive ProxyTop : Ctx -> Type where
  | PTop {ts : Ctx} : ProxyTop (ts + 1)
deriving Repr, DecidableEq
open ProxyTop

class ReifyIndex (ts : Ctx) (ts' : Ctx) where
  reify : ProxyTop ts -> Index ts'
open ReifyIndex

instance instReifyIndexRefl : ReifyIndex ts ts where
  reify
    | PTop => Top

instance instReifyIndexSnoc [instRec : ReifyIndex ts1 ts2] : ReifyIndex ts1 (ts2 + 1) where
  reify := λ p => Pop (reify p)

mutual
  inductive STLC : Ctx -> Type where
    | CVal : Val ts -> STLC ts
    | CVar [inst : ReifyIndex ts ts'] : ProxyTop ts -> STLC ts'
    | CApp : STLC ts -> STLC ts -> STLC ts

  inductive Val : Ctx -> Type where
    | CStar : Val ts
    | CLam (tIn : Ty) (body : ProxyTop (ts + 1) -> STLC (ts + 1)) : Val ts
end
open STLC Val

inductive Lookup : (ts : Ctx) -> Index ts -> Ty -> Type where
  | Top {ts : Ctx} {t : Ty} : Lookup (ts + 1) .Top t
  | Pop {ts : Ctx} {t t' : Ty} {index : Index ts} :
      Lookup ts index t -> Lookup (ts + 1) (.Pop index) t
deriving Repr

inductive HasType : (ts : Ctx) -> STLC ts -> Ty -> Type where
  | CStar {ts : Ctx} : HasType ts (.CVal .CStar) .Unit
  | CLam {ts : Ctx} {tIn tOut : Ty}
      {body : ProxyTop (ts + 1) -> STLC (ts + 1)} :
      ((proxy : ProxyTop (ts + 1)) -> HasType (ts + 1) (body proxy) tOut) ->
      HasType ts (.CVal (.CLam tIn body)) (tIn :-> tOut)
  | CVar {source ts : Ctx} {t : Ty} [inst : ReifyIndex source ts]
      (proxy : ProxyTop source) :
      Lookup ts (ReifyIndex.reify (self := inst) proxy) t ->
      HasType ts (.CVar (inst := inst) proxy) t
  | CApp {ts : Ctx} {tIn tOut : Ty} {fn arg : STLC ts} :
      HasType ts fn (tIn :-> tOut) -> HasType ts arg tIn ->
      HasType ts (.CApp fn arg) tOut

-- Contextualise
-----------------

inductive ProxyVar ts' where
  | PVar [inst : ReifyIndex ts ts'] : ProxyTop ts -> ProxyVar ts'
deriving Repr
open ProxyVar

def weakenPVar : ProxyVar ts' -> ProxyVar (ts' + 1)
  | PVar i => PVar i

def varTop : ProxyVar (ts + 1) := PVar (@PTop ts)

def fromVar : ProxyVar ts' -> STLC ts'
  | PVar i => CVar i

def fromIndex : Index ts -> ProxyVar ts
  | Top   => varTop
  | Pop i => weakenPVar (fromIndex i)

def toCVar : Index ts -> STLC ts
  := λi => fromVar (fromIndex i)

--------------------------------------------
--           Isomorphism proofs           --
--------------------------------------------

/-
De Bruijn and contextually embedded STLC terms correspond very closely, so induction and
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
theorem indexIsoL (i : Index ts')
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
    -- Option 2: `inst` is the Snoc instance, `ts2` must be `ts2' + 1` for some `ts2'`,
    --           and there must be another `ReifyIndex` instance for that `ts2'`.
    --           The `:=` notation passes a value to a named implicit variable.
    --           See: https://lean-lang.org/lean4/doc/lean3changes.html?highlight=named%20implicit%20arguments#function-applications
    (∃(ts2' : Ctx) (hEq : ts2 = ts2' + 1) (inst' : ReifyIndex ts1 ts2'),
       hEq ▸ inst = instReifyIndexSnoc (instRec := inst'))

/-
The `indexIsoR` lemma says that `fromIndex` is the inverse of `reify`.

Here we need to use our `closedWorld` axiom to perform a case analysis on the `ReifyIndex` instance.
-/

theorem indexIsoR (inst : ReifyIndex ts ts') (i : ProxyTop ts):
  (fromIndex (reify (self := inst) i)) = PVar (inst := inst) i
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
        (λ⟨ts2', hEq, inst', instEqSnoc⟩
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
With the index isomorphisms out of the way, the corresponding term isomorphism proofs are almost entirely taken care of by inducting on the term, simplifying with function definitions and the inductive hypotheses, and reflexivity (with normalisation). The only slightly more interesting cases are:

* In `isoL`, `Var` uses the `indexIsoL` isomorphism.
* In `isoR`, `CVar` uses the `indexIsoR` isomorphism and `CLam` uses function extensionality.
-/

-- unembed ∘ contextualise
----------------------------

-- Examples
------------

mutual
  def showSTLC : STLC ts -> String
    | CVal v => showVal v
    | CVar i => "CVar " ++ reprStr i ++ "[reified = " ++ reprStr (reify i : Index ts) ++ "]"
    | CApp f x => "CApp (" ++ showSTLC f ++ ") (" ++ showSTLC x ++ ")"

  def showVal : Val ts -> String
    | CStar => "CStar"
    | CLam _ f => "CLam (\\<ProxyTop> -> " ++ showSTLC (f PTop) ++ ")"
end


def idSTLC {t : Ty} : STLC ts
  := CVal (CLam t (λx => CVar x))
def idSTLC' := @idSTLC 0 Unit

#check idSTLC
#eval showSTLC idSTLC'


def const {t1 t2 : Ty} : STLC ts
  := CVal (CLam t1 (λx => CVal (CLam t2 (λ_y => CVar x))))
def const' := @const 0 Unit Unit

#eval showSTLC const'

def flipConst {t1 t2 : Ty} : STLC ts
  := CVal (CLam t1 (λ_x => CVal (CLam t2 (λy => CVar y))))
def flipConst' := @flipConst 0 Unit Unit

#check flipConst
#eval showSTLC flipConst'


def const5 {t1 t2 t3 t4 t5 : Ty} : STLC ts
  := CVal (CLam t1 (λx1 =>
    CVal (CLam t2 (λ_x2 =>
      CVal (CLam t3 (λ_x3 =>
        CVal (CLam t4 (λ_x4 =>
          CVal (CLam t5 (λ_x5 => CVar x1))))))))))
def const5' := @const5 0 Unit Unit Unit Unit Unit

#eval showSTLC const5'


-- Examples in theorems
------------------------

example {ts : Ctx} {t : Ty}
  : @CLam ts t (λx => CVar x) = @CLam ts t (λy => CVar y) := by
  rfl

end ContextualEmbedding.ExtrinsicTyping.CE
