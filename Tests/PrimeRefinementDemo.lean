import «Tests».PrimeRefinementProvider

namespace Tests.PrimeRefinementDemo

open Tests.PrimeRefinementProvider

section publicApi

example : PrimeNumber :=
  firstPrime

example : firstPrime.belowTen = true := by
  rfl

def extract (v: PrimeNumber) := match v with
  | PrimeNumberRep.mk v i => v

end publicApi

end Tests.PrimeRefinementDemo
