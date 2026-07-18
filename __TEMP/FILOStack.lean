structure Stack (α : Type) where
  items : List α
deriving Repr

namespace Stack

variable {α : Type}

def empty : Stack α :=
  ⟨[]⟩

def push (stack : Stack α) (value : α) : Stack α :=
  ⟨value :: stack.items⟩

def pop? (stack : Stack α) : Option (α × Stack α) :=
  match stack.items with
  | [] => .none
  | value :: items => .some (value, ⟨items⟩)

end Stack

def sampleStack : Stack Nat :=
  Stack.empty
    |>.push 10
    |>.push 20
    |>.push 30

#eval sampleStack
#eval sampleStack.pop?

example : sampleStack.pop? = .some (30, (Stack.empty.push 10).push 20) :=
  rfl

example : (Stack.empty : Stack Nat).pop? = .none :=
  rfl
