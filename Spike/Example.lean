
namespace primary

  def cons (α : Type) (a : α) (as : List α) : List α :=
    List.cons a as

end primary

namespace dual

  structure ConsImpl
    where
    α : Type
    L : Type
    cons (a : α) (as : L) : L

  def getImpl (α : Type) : ConsImpl :=
    ConsImpl.mk α (List α) List.cons

  def cons (α : Type) (a : α) (as : List α) :=
    (getImpl α).cons a as

end dual

namespace induct

def f : Nat → Nat
  | 0     => 1
  | n + 1 => f n + 2

#print f.induct

#print f.induct_unfolding

end induct
