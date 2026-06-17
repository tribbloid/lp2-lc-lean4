import Lean

namespace Tests.PrimeRefinementProvider

/-- A self-contained primality predicate for the refinement demo. -/
def IsPrime (value : Nat) : Prop :=
  And (2 <= value)
    (forall divisor : Nat,
      2 <= divisor ->
      divisor < value ->
      Not (value % divisor = 0))

/-- Private concrete representation of a natural number refined by primality. -/
private structure PrimeNumberRep where
  value : Nat
  isPrime : IsPrime value

/-- Public abstract type for prime natural numbers. -/
abbrev PrimeNumber : Type :=
  PrimeNumberRep

def mkPrimeNumber (value : Nat) (isPrime : IsPrime value) : PrimeNumber :=
  PrimeNumberRep.mk value isPrime

theorem twoIsPrime : IsPrime 2 := by
  constructor
  case left =>
    omega
  case right =>
    intro divisor isTwoLe isLt isDvd
    omega

def firstPrime : PrimeNumber :=
  mkPrimeNumber 2 twoIsPrime

namespace PrimeNumber

def belowTen (self : PrimeNumber) : Bool :=
  self.value < 10

end PrimeNumber

end Tests.PrimeRefinementProvider
