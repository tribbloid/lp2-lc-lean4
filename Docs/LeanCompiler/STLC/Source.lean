namespace LeanCompiler.STLC.Source

inductive Ty : Type where
  | bool : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

infixr:60 " ==> " => Ty.arrow

@[simp] def Ty.denote : Ty → Type
  | .bool => Bool
  | .arrow t1 t2 => Ty.denote t1 → Ty.denote t2

inductive Term (var : Ty → Type) : Ty → Type where
  | var : var t → Term var t
  | tru : Term var .bool
  | fals : Term var .bool
  | app : Term var (t1 ==> t2) → Term var t1 → Term var t2
  | abs : (var t1 → Term var t2) → Term var (t1 ==> t2)

abbrev TermClosed (t : Ty) := (var : Ty → Type) → Term var t

@[simp] def Term.denote : {t : Ty} → Term Ty.denote t → Ty.denote t
  | _, .var v => v
  | _, .tru => true
  | _, .fals => false
  | _, .app e1 e2 => (Term.denote e1) (Term.denote e2)
  | _, .abs e => fun x => Term.denote (e x)

@[simp] def TermClosed.denote {t : Ty} (e : TermClosed t) : Ty.denote t :=
  Term.denote (e Ty.denote)

structure VarPair (var1 var2 : Ty → Type) where
  t : Ty
  v1 : var1 t
  v2 : var2 t

abbrev Ctxt (var1 var2 : Ty → Type) : Type := List (VarPair var1 var2)

@[simp] def mkPair {var1 var2 : Ty → Type} {t : Ty} (v1 : var1 t) (v2 : var2 t) :
    VarPair var1 var2 :=
  ⟨t, v1, v2⟩

inductive TermEquiv {var1 var2 : Ty → Type} :
    Ctxt var1 var2 → {t : Ty} → Term var1 t → Term var2 t → Prop where
  | var {G t} {v1 : var1 t} {v2 : var2 t} :
      mkPair v1 v2 ∈ G →
      TermEquiv G (.var v1) (.var v2)
  | tru {G} : TermEquiv G (.tru (var := var1)) (.tru (var := var2))
  | fals {G} : TermEquiv G (.fals (var := var1)) (.fals (var := var2))
  | app {G t1 t2} {f1 : Term var1 (t1 ==> t2)} {x1 : Term var1 t1}
      {f2 : Term var2 (t1 ==> t2)} {x2 : Term var2 t1} :
      TermEquiv G f1 f2 →
      TermEquiv G x1 x2 →
      TermEquiv G (.app f1 x1) (.app f2 x2)
  | abs {G t1 t2} {f1 : var1 t1 → Term var1 t2} {f2 : var2 t1 → Term var2 t2} :
      (∀ v1 v2, TermEquiv (mkPair v1 v2 :: G) (f1 v1) (f2 v2)) →
      TermEquiv G (.abs f1) (.abs f2)

class TermParametricity : Prop where
  closed :
    ∀ {t : Ty} (E : TermClosed t) (var1 var2 : Ty → Type),
      TermEquiv ([] : Ctxt var1 var2) (E var1) (E var2)

theorem termEquivClosed [TermParametricity] :
  ∀ {t : Ty} (E : TermClosed t) (var1 var2 : Ty → Type),
    TermEquiv ([] : Ctxt var1 var2) (E var1) (E var2) :=
  TermParametricity.closed

end LeanCompiler.STLC.Source
