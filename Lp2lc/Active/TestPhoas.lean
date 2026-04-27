import Lp2lc.Active.phoas

namespace NbETest

def Value (rep : Ty → Type) : Ty → Type
  | Ty.nat => Term' rep Ty.nat
  | Ty.fn a b => Value rep a → Value rep b

mutual
  def reify (rep : Ty → Type) : (ty : Ty) → Value rep ty → Term' rep ty
    | Ty.nat, v => v
    | Ty.fn a b, f => Term'.lam (fun x => reify rep b (f (reflect rep a (Term'.var x))))

  def reflect (rep : Ty → Type) : (ty : Ty) → Term' rep ty → Value rep ty
    | Ty.nat, v => v
    | Ty.fn a b, v => fun x => reflect rep b (Term'.app v (reify rep a x))
end

def eval (rep : Ty → Type) : (ty : Ty) → Term' (Value rep) ty → Value rep ty
  | _, Term'.var v => v
  | _, Term'.const n => reflect rep Ty.nat (Term'.const n)
  | _, Term'.plus a b =>
    match reify rep Ty.nat (eval rep Ty.nat a), reify rep Ty.nat (eval rep Ty.nat b) with
    | Term'.const n, Term'.const m => reflect rep Ty.nat (Term'.const (n + m))
    | a', b' => reflect rep Ty.nat (Term'.plus a' b')
  | _, @Term'.lam _ dom ran f => fun x => eval rep ran (f x)
  | _, @Term'.app _ dom ran f a => (eval rep (Ty.fn dom ran) f) (eval rep dom a)
  | _, @Term'.let _ ty1 ty2 a b => eval rep ty2 (b (eval rep ty1 a))

def normalize (ty : Ty) (e : Term ty) : Term ty :=
  fun {rep} => reify rep ty (eval rep ty (e (rep := Value rep)))

def eval_three (rep : Ty → Type) : normalize Ty.nat three_the_hard_way (rep := rep) = Term'.const 3 := rfl

end NbETest
