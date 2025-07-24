import Mathlib.Tactic

-- An example proof with multiple subgoals.
-- The `cases` tactic splits the goal into two subgoals,
-- one for `n = 0` and one for `n > 0`.
theorem zero_or_pos (n : Nat) : n = 0 ∨ n > 0 := by
  cases n
  -- After `cases n`, we have two goals:
  -- 1. ⊢ 0 = 0 ∨ 0 > 0
  -- 2. ⊢ Nat.succ n = 0 ∨ Nat.succ n > 0
  case zero =>
    -- We are now working on the first goal.
    left
    rfl
  case succ n' =>
    -- We are now working on the second goal.
    right
    exact Nat.succ_pos n'

-- An example proof with multiple hypotheses in the context.
-- The `intro` tactic moves premises of an implication into the
-- local context as hypotheses.
theorem add_pos_of_pos (a b : Nat) : a > 0 → b > 0 → a + b > 0 := by
  -- `intro ha` adds `ha : a > 0` to the context.
  intro ha
  -- `intro hb` adds `hb : b > 0` to the context.
  intro hb
  -- The context now contains `ha` and `hb`, which we can use.
  -- State:
  -- a b : Nat
  -- ha : a > 0
  -- hb : b > 0
  -- ⊢ a + b > 0
  exact add_pos ha hb

-- Yes, the `revert` tactic can be used with inequalities.
-- `revert` moves a hypothesis from the context back into the goal.
-- This is often used to generalize a statement before applying induction
-- or another tactic that works on the whole goal.

theorem revert_inequality_example (n m : Nat) (h : n ≤ m) : n ≤ m + 1 := by
  -- The initial state has `h : n ≤ m` in the context.
  -- State:
  -- n m : Nat
  -- h : n ≤ m
  -- ⊢ n ≤ m + 1

  -- We could prove this directly, but let's use `revert` to show how it works.
  revert m

  -- After `revert m`, the variable `m` and the hypothesis `h` which depends on it
  -- are moved back into the goal.
  -- State:
  -- n : Nat
  -- ⊢ ∀ (m : Nat), n ≤ m → n ≤ m + 1

  -- We can now introduce them back and prove the goal.
  intro m' h'
  exact Nat.le_succ_of_le h'

-- To convert a goal from `a < b` to `b > a`, you can use the `change` tactic.
-- This works because `a < b` is definitionally equivalent to `b > a`.
theorem convert_lt_to_gt_example (a b : Nat) (h : b > a) : a < b := by
  -- The initial goal is `a < b`.
  change b > a
  -- The goal is now `b > a`.
  exact h

-- The reverse is also possible.
theorem convert_gt_to_lt_example (a b : Nat) (h : a < b) : b > a := by
  -- The initial goal is `b > a`.
  change a < b
  -- The goal is now `a < b`.
  exact h

-- To split a goal of the form `P ∧ Q` into two separate goals (`P` and `Q`),
-- you can use the `constructor` tactic.
theorem split_conjunction_goal (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  -- The initial goal is to prove `p ∧ q`.
  constructor
  -- After `constructor`, we have two goals:
  -- 1. ⊢ p
  -- 2. ⊢ q
  -- Prove the first goal.
  exact hp
  -- Prove the second goal.
  exact hq

example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- Goal: x y : Nat ⊢ x = y → y = x
  intro h₁
  apply Eq.symm
  assumption
