namespace Tests.ParametricityNaturalityDemo

abbrev TypeFamily := Type → Type

def Graph {A B : Type} (f : A → B) : A → B → Prop :=
  λ x y => f x = y

structure RelationalType (G : TypeFamily) where
  map : {A B : Type} → (f : A → B) → (x : G A) → G B
  rel : {A B : Type} → (R : A → B → Prop) → (x : G A) → (y : G B) → Prop
  relGraph : ∀ {A B : Type} (f : A → B) (x : G A) (y : G B),
    rel (Graph f) x y ↔ map f x = y

abbrev PolyFunction (G : TypeFamily) :=
  {A : Type} → (x : A) → G A

structure ParametricFunction
    {G : TypeFamily}
    (relG : RelationalType G) where
  toFun : PolyFunction G
  preservesRelation : ∀ {A B : Type} (R : A → B → Prop) (x : A) (y : B),
    R x y → relG.rel R (toFun x) (toFun y)

instance {G : TypeFamily} {relG : RelationalType G} :
    CoeFun (ParametricFunction relG) (λ _ => PolyFunction G) where
  coe self := self.toFun

structure NaturalFunction
    {G : TypeFamily}
    (relG : RelationalType G) where
  toFun : PolyFunction G
  naturality : ∀ {A B : Type} (f : A → B) (x : A),
    relG.map f (toFun x) = toFun (f x)

instance {G : TypeFamily} {relG : RelationalType G} :
    CoeFun (NaturalFunction relG) (λ _ => PolyFunction G) where
  coe self := self.toFun

def ParametricFunction.toNatural
    {G : TypeFamily}
    {relG : RelationalType G}
    (self : ParametricFunction relG) : NaturalFunction relG where
  toFun := self.toFun
  naturality := by
    intro A B f x
    apply (relG.relGraph f (self x) (self (f x))).mp
    apply self.preservesRelation (Graph f) x (f x)
    rfl

end Tests.ParametricityNaturalityDemo
