
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
