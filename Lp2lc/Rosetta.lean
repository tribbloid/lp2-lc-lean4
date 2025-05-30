
-- scope section
namespace Rosetta

  namespace Basic

    -- type
    def T1 : Type := String

    -- proposition
    def P1: Prop := 2 + 2 = 4

    -- instance / inhabitant / example
    def v1 : T1 := "hello"

    -- proving automatically
    def p1: P1 := rfl

    section

      -- type definition pending or left as an exercise
      def T : Type := sorry

      -- inhabitant / example pending or left as an exercise
      def v: T := sorry

    end

  end Basic

  -- constructive
  -- no complement
  -- no law of excluded middle
  namespace Constructive

    -- system lambda / simply-typed lambda calculus
    -- propositional logic
    namespace SimpleTypes
      def A : Type := sorry
      def B : Type := sorry

      -- function / lambda
      -- if v satisfy A, then fn(v) satisfy B
      namespace function
        def fn1(v : A) : B := sorry
        def fn2: A -> B := sorry
      end function

      -- product type
      -- if a and b satisfy A and B respectively, then fn(a, b) satisfy C
      namespace product

        def C1 : Type := sorry
        def fn1(a: A) (b: B) : C1 := sorry

        structure C2 :=
          (a : A)
          (b : B)
      end product

      -- sum/inductive type
      -- if v satisfy A or B, then fn1(v) or fn2(v) satisfy C
      namespace sum

        inductive C1 : Type :=
          | fn1 (v : A) : C1
          | fn2 (v : B) : C1

        -- infinite / structural
        section

          inductive Nat1 : Type :=
            | zero : Nat1
            | succeed (n : Nat1) : Nat1

        end
      end sum

    end SimpleTypes

    -- system lambdaP
    -- predicative logic
    namespace DependentTypes

      -- dependent type
      -- type F(?) that depends on an example of type A
      structure A1
        where (F : Type)

      def A2 : Type := sorry
      def B2: Prop := sorry

      def K1(v: A2) : Type := sorry
      def K2 : B2 -> Prop := sorry

      class HasD (v: A2)
        where (D : Type)

      -- dependent Pi type
      -- universal quantifier
      -- for all v that satisfy A, fn(v) always satisfy D(v)
      namespace universal

        def f1 (v : A1) : v.F := sorry

        def f2 : (v: A1) -> v.F := sorry

        def f3 : ∀ (v : A1), v.F := sorry

        #check f1 = f2
        #check f1 = f3

        def g1 : (v : A2) -> K1 v := sorry

        def g2 : ∀ (v : A2), K1 v := sorry

        #check g1 = g2

      end universal

      -- dependent Sigma type
      -- existential quantifier
      -- if v satisfy A, at least one v2 can be found to satisfy D(v), such that fn(v)(v2) satisfy B
      namespace existential

        abbrev F1 : Type 1 := (v: A1) × v.F -- TODO: WTF? why is it not Type 0? Like G1

        def f1: F1 := sorry
        def f2: Σ (v: A1), v.F := sorry

        #check f1 = f2

        abbrev G1 : Type 0 := (v: A2) × K1 v
        abbrev G2 : Type 0 := Σ (v: A2), K1 v

        #check G1 = G2

        def g1: G1 := sorry
        def g2: G2 := g1

        #check g1 = g2

        def a2 : A2 := sorry

        -- def h1: Σ (v: B2), F2 v := sorry -- won't work
        def h2: ∃ (v: B2), K2 v := sorry

      end existential
    end DependentTypes

    -- system lambda2 / F
    -- 2nd order propositional logic
    namespace PolymorphicTypes

      def B : Type := sorry

      -- parametric
      -- example fn(?) of type B that depends on a type
      -- for all A that can be satisfied / for the whole collection that satisfy A
      --  ... B has a constructive proof fn(A)
      namespace parametric

        def fn1(T : Type) : B := sorry
        def fn2 : Type -> B := sorry

        class TypeCls (T : Type)
          where f : B

        instance _1 : TypeCls T := sorry

        def fn3[TypeCls T] := TypeCls.f

      end parametric

      -- ad-hoc
      -- for all A that can be satisfied and can be covered by several cases / for several collections that constitutes A
      --  ... each one has a different constructive proof for B
      namespace adhoc

        class TypeCls (T : Type)
          where f : B

        instance _1 : TypeCls Nat := sorry
        instance _2 : TypeCls String := sorry

        def fn[TypeCls T] := TypeCls.f

      end adhoc
    end PolymorphicTypes

    namespace HigherKinds


    end HigherKinds

  end Constructive

end Rosetta
