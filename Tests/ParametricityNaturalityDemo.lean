namespace Tests.ParametricityNaturalityDemo

universe u

abbrev TypeFamily := Type u → Type u

def Graph {A B : Type u} (f : A → B) : A → B → Prop :=
  λ x y => f x = y

structure RelationalType (F : TypeFamily) where
  map : {A B : Type u} → (f : A → B) → (x : F A) → F B
  rel : {A B : Type u} → (R : A → B → Prop) → (x : F A) → (y : F B) → Prop
  relGraph : ∀ {A B : Type u} (f : A → B) (x : F A) (y : F B),
    rel (Graph f) x y ↔ map f x = y

abbrev PolymorphicFunction (F G : TypeFamily) :=
  {A : Type u} → (x : F A) → G A

structure ParametricFunction
    {F G : TypeFamily}
    (relF : RelationalType F)
    (relG : RelationalType G) where
  toFun : PolymorphicFunction F G
  preservesRelation : ∀ {A B : Type u} (R : A → B → Prop) (x : F A) (y : F B),
    relF.rel R x y → relG.rel R (toFun x) (toFun y)

instance {F G : TypeFamily} {relF : RelationalType F} {relG : RelationalType G} :
    CoeFun (ParametricFunction relF relG) (λ _ => PolymorphicFunction F G) where
  coe self := self.toFun

structure NaturalFunction
    {F G : TypeFamily}
    (relF : RelationalType F)
    (relG : RelationalType G) where
  toFun : PolymorphicFunction F G
  naturality : ∀ {A B : Type u} (f : A → B) (x : F A),
    relG.map f (toFun x) = toFun (relF.map f x)

instance {F G : TypeFamily} {relF : RelationalType F} {relG : RelationalType G} :
    CoeFun (NaturalFunction relF relG) (λ _ => PolymorphicFunction F G) where
  coe self := self.toFun

def ParametricFunction.toNatural
    {F G : TypeFamily}
    {relF : RelationalType F}
    {relG : RelationalType G}
    (self : ParametricFunction relF relG) : NaturalFunction relF relG where
  toFun := self.toFun
  naturality := by
    intro A B f x
    apply (relG.relGraph f (self x) (self (relF.map f x))).mp
    apply self.preservesRelation (Graph f) x (relF.map f x)
    exact (relF.relGraph f x (relF.map f x)).mpr rfl

end Tests.ParametricityNaturalityDemo
