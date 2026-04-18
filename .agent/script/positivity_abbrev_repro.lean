abbrev Alias (α : Type) := Option α

inductive I1 : Type where
| mk : Option I1 → I1

/-- error: (kernel) arg #1 of I2.mk' contains a non valid occurrence of the datatypes being declared -/
#guard_msgs in
inductive I2 : Type where
| mk : Alias I2 → I2
