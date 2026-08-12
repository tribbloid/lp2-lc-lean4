namespace Phoas.Extrinsic

inductive Ty where
  | nat
  | fn (dom ran : Ty)
  deriving DecidableEq

@[reducible] def Ty.denote : Ty → Type
  | Ty.nat => Nat
  | Ty.fn dom ran => Ty.denote dom → Ty.denote ran

def v1 :=
  let ty := Ty.nat
  ty.denote

example : v1 = Nat :=
  rfl

inductive Term' (rep : Type) where
  | var (x : rep)
  | const (n : Nat)
  | plus (left right : Term' rep)
  | lam (dom : Ty) (body : rep → Term' rep)
  | app (function argument : Term' rep)
  | let (value : Term' rep) (body : rep → Term' rep)

def infer (load : rep → Ty) (save : Ty → rep) : Term' rep → Option Ty
  | Term'.var x => some (load x)
  | Term'.const _ => some Ty.nat
  | Term'.plus left right =>
    match infer load save left, infer load save right with
    | some Ty.nat, some Ty.nat => some Ty.nat
    | _, _ => none
  | Term'.lam dom body =>
    match infer load save (body (save dom)) with
    | some ran => some (Ty.fn dom ran)
    | none => none
  | Term'.app function argument =>
    match infer load save function, infer load save argument with
    | some (Ty.fn dom ran), some arg =>
      if dom = arg then some ran else none
    | _, _ => none
  | Term'.let value body =>
    match infer load save value with
    | some ty => infer load save (body (save ty))
    | none => none

def HasType (term : Term' Ty) (ty : Ty) : Prop :=
  infer id id term = some ty

namespace FirstTry

def Term := (rep : Type) → Term' rep

def add : Term := λ _rep =>
  Term'.lam Ty.nat (λ x =>
    Term'.lam Ty.nat (λ y =>
      Term'.plus (Term'.var x) (Term'.var y)))

def three_the_hard_way : Term := λ rep =>
  Term'.app (Term'.app (add rep) (Term'.const 1)) (Term'.const 2)

example : HasType (add Ty) (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  rfl

example : HasType (three_the_hard_way Ty) Ty.nat :=
  rfl

end FirstTry

def Term := {rep : Type} → Term' rep

namespace Term

def HasType (term : Term) (ty : Ty) : Prop :=
  infer id id term = some ty

end Term

def add : Term :=
  Term'.lam Ty.nat (λ x =>
    Term'.lam Ty.nat (λ y =>
      Term'.plus (Term'.var x) (Term'.var y)))

def three_the_hard_way : Term :=
  Term'.app (Term'.app add (Term'.const 1)) (Term'.const 2)

example : add.HasType (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  rfl

example : three_the_hard_way.HasType Ty.nat :=
  rfl

def countVars : Term' Unit → Nat
  | Term'.var _ => 1
  | Term'.const _ => 0
  | Term'.plus left right => countVars left + countVars right
  | Term'.app function argument => countVars function + countVars argument
  | Term'.lam _ body => countVars (body ())
  | Term'.let value body => countVars value + countVars (body ())

example : countVars add = 2 :=
  rfl

def pretty (term : Term' String) (index : Nat := 1) : String :=
  match term with
  | Term'.var name => name
  | Term'.const n => toString n
  | Term'.app function argument => s!"({pretty function index} {pretty argument index})"
  | Term'.plus left right => s!"({pretty left index} + {pretty right index})"
  | Term'.lam _ body =>
    let name := s!"x_{index}"
    s!"(fun {name} => {pretty (body name) (index + 1)})"
  | Term'.let value body =>
    let name := s!"x_{index}"
    s!"(let {name} := {pretty value index}; => {pretty (body name) (index + 1)}"

#eval pretty three_the_hard_way

def squash : Term' (Term' rep) → Term' rep
  | Term'.var term => term
  | Term'.const n => Term'.const n
  | Term'.plus left right => Term'.plus (squash left) (squash right)
  | Term'.lam dom body => Term'.lam dom (λ x => squash (body (Term'.var x)))
  | Term'.app function argument => Term'.app (squash function) (squash argument)
  | Term'.let value body => Term'.let (squash value) (λ x => squash (body (Term'.var x)))

def Term1 := {rep : Type} → rep → Term' rep

namespace Term1

def HasType (term : Term1) (dom ran : Ty) : Prop :=
  infer id id (term dom) = some ran

end Term1

def subst (term : Term1) (replacement : Term) : Term :=
  squash (term replacement)

#eval pretty <| subst (λ x => Term'.plus (Term'.var x) (Term'.const 5)) three_the_hard_way

@[reducible] def Ty.denotePartial : Ty → Type
  | Ty.nat => Nat
  | Ty.fn dom ran => Ty.denotePartial dom → Option (Ty.denotePartial ran)

def Ty.defaultPartial : (ty : Ty) → ty.denotePartial
  | Ty.nat => 0
  | Ty.fn _ _ => λ _ => none

structure Value where
  ty : Ty
  value : ty.denotePartial

def Value.ofType (ty : Ty) : Value :=
  ⟨ty, ty.defaultPartial⟩

def denoteAt : (ty : Ty) → Term' Value → Option ty.denotePartial
  | ty, Term'.var boundValue =>
    if h : boundValue.ty = ty then
      some (h ▸ boundValue.value)
    else
      none
  | Ty.nat, Term'.const n => some n
  | Ty.fn _ _, Term'.const _ => none
  | Ty.nat, Term'.plus left right => do
    let leftValue ← denoteAt Ty.nat left
    let rightValue ← denoteAt Ty.nat right
    pure (leftValue + rightValue)
  | Ty.fn _ _, Term'.plus _ _ => none
  | Ty.nat, Term'.lam _ _ => none
  | Ty.fn dom ran, Term'.lam annotatedDom body =>
    if h : annotatedDom = dom then
      some (λ x => denoteAt ran (body ⟨annotatedDom, h.symm ▸ x⟩))
    else
      none
  | ty, Term'.app function argument =>
    match infer Value.ty Value.ofType function with
    | some (Ty.fn dom ran) =>
      if h : ran = ty then
        h ▸ do
          let functionValue ← denoteAt (Ty.fn dom ran) function
          let argumentValue ← denoteAt dom argument
          functionValue argumentValue
      else
        none
    | _ => none
  | ty, Term'.let value body =>
    match infer Value.ty Value.ofType value with
    | some valueTy => do
      let denotedValue ← denoteAt valueTy value
      denoteAt ty (body ⟨valueTy, denotedValue⟩)
    | none => none

def denote (term : Term) : Option Value :=
  match infer id id term with
  | some ty => do
    let value ← denoteAt ty term
    pure ⟨ty, value⟩
  | none => none

example : denote three_the_hard_way = some ⟨Ty.nat, 3⟩ :=
  rfl

@[simp] def constFold : Term' rep → Term' rep
  | Term'.var x => Term'.var x
  | Term'.const n => Term'.const n
  | Term'.app function argument => Term'.app (constFold function) (constFold argument)
  | Term'.lam dom body => Term'.lam dom (λ x => constFold (body x))
  | Term'.let value body => Term'.let (constFold value) (λ x => constFold (body x))
  | Term'.plus left right =>
    match constFold left, constFold right with
    | Term'.const n, Term'.const m => Term'.const (n + m)
    | left', right' => Term'.plus left' right'

theorem infer_constFold (term : Term' rep) :
    infer typeOf fresh (constFold term) = infer typeOf fresh term := by
  induction term with
  | var
  | const =>
    rfl
  | plus left right ihLeft ihRight =>
    simp only [infer]
    rw [← ihLeft, ← ihRight]
    simp only [constFold]
    generalize constFold left = foldedLeft
    generalize constFold right = foldedRight
    cases foldedLeft <;> cases foldedRight <;> rfl
  | lam dom body ih =>
    simp [infer, ih]
  | app function argument ihFunction ihArgument =>
    simp [infer, ihFunction, ihArgument]
  | «let» value body ihValue ihBody =>
    simp [infer, ihValue, ihBody]

theorem constFold_sound (ty : Ty) (term : Term' Value) :
    denoteAt ty (constFold term) = denoteAt ty term := by
  induction term generalizing ty with
  | var =>
    simp [denoteAt]
  | const =>
    cases ty <;> rfl
  | plus left right ihLeft ihRight =>
    cases ty with
    | nat =>
      simp only [constFold, denoteAt]
      rw [← ihLeft Ty.nat, ← ihRight Ty.nat]
      generalize constFold left = foldedLeft
      generalize constFold right = foldedRight
      cases foldedLeft <;> cases foldedRight <;> rfl
    | fn dom ran =>
      simp only [constFold]
      generalize constFold left = foldedLeft
      generalize constFold right = foldedRight
      cases foldedLeft <;> cases foldedRight <;> rfl
  | lam dom body ih =>
    cases ty with
    | nat =>
      rfl
    | fn expectedDom ran =>
      simp only [constFold, denoteAt]
      split
      · congr 2
        funext value
        apply ih
      · rfl
  | app function argument ihFunction ihArgument =>
    simp [denoteAt, infer_constFold, ihFunction, ihArgument]
  | «let» value body ihValue ihBody =>
    simp [denoteAt, infer_constFold, ihValue, ihBody]

namespace NbE

abbrev Value (rep : Type) := Term' rep

def eval : Nat → Term' (Value rep) → Term' (Value rep)
  | 0, term => term
  | _ + 1, Term'.var value => Term'.var value
  | _ + 1, Term'.const n => Term'.const n
  | fuel + 1, Term'.plus left right =>
    let left' := eval fuel left
    let right' := eval fuel right
    match squash left', squash right' with
    | Term'.const n, Term'.const m => Term'.const (n + m)
    | _, _ => Term'.plus left' right'
  | fuel + 1, Term'.lam dom body => Term'.lam dom (λ x => eval fuel (body x))
  | fuel + 1, Term'.app function argument =>
    let function' := eval fuel function
    let argument' := eval fuel argument
    match function' with
    | Term'.lam _ body => eval fuel (body (squash argument'))
    | _ => Term'.app function' argument'
  | fuel + 1, Term'.let value body =>
    let value' := eval fuel value
    eval fuel (body (squash value'))

def normalize (term : Term) : Term :=
  λ {rep} =>
    squash (eval 16 (term (rep := Value rep)))

theorem eval_three {rep : Type} :
    normalize three_the_hard_way (rep := rep) = Term'.const 3 :=
  rfl

end NbE

def assumedPureIncrement : Term :=
  Term'.lam Ty.nat (λ x => Term'.plus (Term'.var x) (Term'.const 1))

def pureIncrementOnConst : Term :=
  Term'.app assumedPureIncrement (Term'.const 41)

example : assumedPureIncrement.HasType (Ty.fn Ty.nat Ty.nat) :=
  rfl

example : pureIncrementOnConst.HasType Ty.nat :=
  rfl

example : denote pureIncrementOnConst = some ⟨Ty.nat, 42⟩ :=
  rfl

example {rep : Type} :
    constFold (pureIncrementOnConst (rep := rep)) =
      Term'.app
        (Term'.lam Ty.nat (λ x => Term'.plus (Term'.var x) (Term'.const 1)))
        (Term'.const 41) :=
  rfl

example {rep : Type} :
    NbE.normalize pureIncrementOnConst (rep := rep) = Term'.const 42 :=
  rfl

end Phoas.Extrinsic
