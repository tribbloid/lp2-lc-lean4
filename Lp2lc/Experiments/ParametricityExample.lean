

structure ParametricPoly (OK : Type -> Type) where
  body: ∀ (I : Type), (I -> (OK I))

open Classical

/-- Relational parametricity (the free theorem) that an inhabitant of
`∀ (I : Type), I → I` must satisfy to be considered parametric. -/
def ParametricId (f : ∀ (I : Type), I → I) : Prop :=
  ∀ (A B : Type) (R : A → B → Prop) (x : A) (y : B), R x y → R (f A x) (f B y)

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
