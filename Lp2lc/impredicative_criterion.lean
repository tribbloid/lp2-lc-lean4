namespace criterion

  def KP(T : Prop): Prop := sorry
  def KT(T : Type): Type := sorry

  abbrev PCtor : Prop := ∀ (P : Prop), KP P -- safe

  abbrev T1_bad : Type := (Type) -> Unit -- unsafe! prone to paradox
  abbrev TCtor1 : Type 1 := (Type) -> Unit -- safe

  structure Singleton

  def getOnlyTerm (T : Type)[Coe T Singleton] : T := sorry
  def downcast(T : Type)(s : Singleton) : T := sorry -- compile-time check for [Coe (s: Singleton) T]

  abbrev TCtor2: Type 1 := ∀ (T : Type) [Coe T Singleton], KT T
  abbrev TCtor2_dual : Type := Singleton -> Singleton -- safe again, despite being defined in Type 0

  def convertBack(T : Type)(src: TCtor2_dual)[Coe T Singleton][Coe (KT T) Singleton]: TCtor2 :=
    fun (T : Type) [Coe T Singleton] =>
      let s1: T := getOnlyTerm T
      let s2: Singleton := src s1
      downcast (KT T) s2

end criterion
