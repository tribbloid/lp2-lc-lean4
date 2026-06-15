

section variable (fuel: Nat)

def f1 : Unit :=
    match fuel with
    | 0 => Unit.unit
    | less + 1 => f1 less

def f2 (fuel: Nat) : Unit :=
    match fuel with
    | 0 => Unit.unit
    | less + 1 => f2 less

end
