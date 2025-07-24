import Lean

-- Example demonstrating how to call one elaborator from another
-- This shows the basic pattern for composing elaborators

open Lean Elab Term Meta

-- First elaborator: simple one that creates a natural number literal
elab "make_nat" n:num : term => do
  -- line 10: Basic elaborator that converts syntax number to Expr
  let natVal := n.getNat
  return mkNatLit natVal

-- Second elaborator: calls the first elaborator internally
elab "double_nat" n:num : term => do
  -- line 15: More complex elaborator that calls another elaborator
  -- Step 1: Create syntax for the first elaborator call
  let natSyntax := Syntax.mkNumLit (toString n.getNat)
  let makeNatStx := Syntax.node SourceInfo.none `null #[Syntax.atom SourceInfo.none "make_nat", natSyntax]

  -- Step 2: Elaborate the syntax using the first elaborator
  let natExpr ← elabTerm makeNatStx none

  -- Step 3: Create an expression that doubles the result
  let two := mkNatLit 2
  let doubled ← mkAppM `Nat.mul #[two, natExpr]

  return doubled

-- Third elaborator: demonstrates calling elaborators with different approaches
elab "triple_using_direct_call" n:num : term => do
  -- line 28: Alternative approach - directly calling elaboration functions
  let natVal := n.getNat
  let baseExpr := mkNatLit natVal
  let three := mkNatLit 3
  let tripled ← mkAppM `Nat.mul #[three, baseExpr]
  return tripled

-- Fourth elaborator: shows how to call elaborators recursively
elab "factorial_like" n:num : term => do
  -- line 36: Recursive-style elaborator calls
  let natVal := n.getNat
  if natVal ≤ 1 then
    return mkNatLit 1
  else
    -- Create syntax for recursive call
    let prevNum := natVal - 1
    let prevSyntax := Syntax.mkNumLit (toString prevNum)
    let factStx := Syntax.node SourceInfo.none `null #[
      Syntax.atom SourceInfo.none "factorial_like",
      prevSyntax
    ]

    -- Elaborate the recursive call
    let prevResult ← elabTerm factStx none

    -- Multiply by current number
    let currNum := mkNatLit natVal
    let result ← mkAppM `Nat.mul #[currNum, prevResult]
    return result

-- Example usage and tests
#check make_nat 5              -- line 54: Should be 5
#check double_nat 7            -- line 55: Should be 14
#check triple_using_direct_call 4  -- line 56: Should be 12
#check factorial_like 4        -- line 57: Should be 24

-- Evaluation examples to see the results
#eval make_nat 5               -- line 60: 5
#eval double_nat 7             -- line 61: 14
#eval triple_using_direct_call 4   -- line 62: 12
#eval factorial_like 4         -- line 63: 24

-- Advanced example: elaborator that takes syntax and calls other elaborators
syntax "compute_series" num : term

elab_rules : term
| `(compute_series $n) => do
  -- line 68: Pattern matching on syntax and calling multiple elaborators
  let natVal := n.getNat

  -- Call make_nat elaborator
  let singleSyntax := Syntax.mkNumLit (toString natVal)
  let makeNatStx := Syntax.node SourceInfo.none `null #[Syntax.atom SourceInfo.none "make_nat", singleSyntax]
  let single ← elabTerm makeNatStx none

  -- Call double_nat elaborator
  let doubleStx := Syntax.node SourceInfo.none `null #[Syntax.atom SourceInfo.none "double_nat", singleSyntax]
  let double ← elabTerm doubleStx none

  -- Call triple_using_direct_call elaborator
  let tripleStx := Syntax.node SourceInfo.none `null #[Syntax.atom SourceInfo.none "triple_using_direct_call", singleSyntax]
  let triple ← elabTerm tripleStx none

  -- Combine results: single + double + triple
  let sum1 ← mkAppM `Nat.add #[single, double]
  let finalSum ← mkAppM `Nat.add #[sum1, triple]

  return finalSum

#eval compute_series 3  -- line 86: Should be 3 + 6 + 9 = 18
