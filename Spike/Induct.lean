
namespace induct

def f : Nat → Nat
  | 0     => 1
  | n + 1 => f n + 2

#print f.induct

#print f.induct_unfolding

end induct
