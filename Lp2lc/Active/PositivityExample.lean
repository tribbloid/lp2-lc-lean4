import Std

namespace Lp2lc.Active.Dot.PositivityExample

namespace FunctionAlias

def Lookup (K V : Type) := K → Option V

/-- error: (kernel) arg #1 of 'Lp2lc.Active.Dot.PositivityExample.FunctionAlias.Val.object' contains a non valid occurrence of the datatypes being declared -/
#guard_msgs in
inductive Val : Type where
| atom : Val
| object : Lookup String Val → Val

end FunctionAlias

namespace OpaqueAlias

opaque Lookup (K V : Type) : Type := K → Option V

/-- error: (kernel) arg #1 of 'Lp2lc.Active.Dot.PositivityExample.OpaqueAlias.Val.object' contains a non valid occurrence of the datatypes being declared -/
#guard_msgs in
inductive Val : Type where
| atom : Val
| object : Lookup String Val → Val

end OpaqueAlias

namespace Structure

structure Lookup (K V : Type) where
  underlying : K → Option V

inductive Val : Type where
| atom : Val
| object : Lookup String Val → Val

end Structure

end Lp2lc.Active.Dot.PositivityExample
