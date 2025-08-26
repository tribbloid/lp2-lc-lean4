import Lean

def sumList (xs : List Nat) : Nat := -- works
  Id.run do
    let mut acc := 0
    for x in xs do
      acc := acc + x
    return acc


-- def sumList2 (xs : List Nat) : Nat := -- doesn't
--     let mut acc := 0
--     for x in xs do
--       acc := acc + x
--     acc
