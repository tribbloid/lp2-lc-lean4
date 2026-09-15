namespace guard

unsafe def fImpl (x : Nat) : Nat :=
  x + 1

@[implemented_by fImpl]
opaque f (x : Nat) : Nat

#guard f 10 == 11

#guard f 10 = 11

/-- info: 11 -/
#guard_msgs in
#eval f 10

end guard
