

structure ParametricPoly (OK : Type -> Type) where
  body: ∀ (I : Type), (I -> (OK I))

open Classical

/-- Relational parametricity (the free theorem) that an inhabitant of
`∀ (I : Type), I → I` must satisfy to be considered parametric. -/
def ParametricId (f : ∀ (I : Type), I → I) : Prop :=
  ∀ (A B : Type) (R : A → B → Prop) (x : A) (y : B), R x y → R (f A x) (f B y)

/-- The polymorphic identity satisfies its free theorem: its outputs reduce
definitionally to its inputs, so the conclusion `R (f A x) (f B y)` is the
hypothesis `R x y`. Hence `ParametricId` is satisfiable. -/
theorem idParametric : ParametricId (λ _ x => x) :=
  λ _ _ _ _ _ hxy => hxy

/-- Conversely, any `f` satisfying `ParametricId` must be pointwise the
identity: instantiate the relation at `R _ b := (b = x)`, which holds on the
input pair `x, x` by `rfl` and forces `f A x = x` in the conclusion. The
quantification over *all* relations is so strong that at most one `f` obeys
it. -/
theorem parametricId_eq_identity (f : ∀ (I : Type), I → I) (h : ParametricId f)
    (A : Type) (x : A) : f A x = x :=
  h A A (λ _ b => b = x) x x rfl

/-- `ParametricId` characterizes a singleton: exactly the polymorphic
identity. -/
theorem parametricId_iff_identity (f : ∀ (I : Type), I → I) :
    ParametricId f ↔ f = λ _ x => x :=
  ⟨λ h => funext λ A => funext (parametricId_eq_identity f h A),
   λ h => h.symm ▸ idParametric⟩

/-- A well-typed inhabitant of `∀ (I : Type), I → I` that inspects its type
argument through classical decidability of type equality, hence not parametric.
The noncomputability is inherent: type equality is not decidable. -/
noncomputable def cheat : ∀ (I : Type), I → I :=
  λ I x =>
    if h : I = Nat then
      h.symm ▸ (0 : Nat)
    else x

/-- `cheat` is the constant zero on `Nat`, so it is not the identity. -/
theorem cheat_nat (x : Nat) : cheat Nat x = 0 := by
  unfold cheat
  exact dif_pos rfl

/-- `cheat` violates the free theorem, so the type of `ParametricPoly.body`
does not enforce parametricity. -/
theorem cheat_not_parametric : ¬ ParametricId cheat :=
  λ h =>
    absurd (h Nat Nat (λ a b : Nat => a = 0 ∧ b = 1) 0 1 ⟨rfl, rfl⟩)
      (by simp [cheat_nat])

example : cheat Nat 1 ≠ 1 := by
  simp [cheat_nat]

/-- Instantiating `OK I := I`, `cheat` is a well-typed `body` that is not
parametric. -/
noncomputable def cheatPoly : ParametricPoly (λ (I : Type) => I) :=
  ⟨cheat⟩

#print axioms cheat_not_parametric
