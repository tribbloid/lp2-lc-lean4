namespace Lp2lc.Active

namespace PartialDefInheritance

inductive BaseCmd where
  | halt : Nat → BaseCmd
  | tick : BaseCmd → BaseCmd

partial def run_base_cmd : BaseCmd → Nat
  | .halt n => n
  | .tick next => run_base_cmd next + 1

inductive ExtendedCmd where
  | base : BaseCmd → ExtendedCmd
  | twice : ExtendedCmd → ExtendedCmd

partial def run_extended_cmd : ExtendedCmd → Nat
  | .base cmd => run_base_cmd cmd
  | .twice cmd => run_extended_cmd cmd * 2

def inherited_arartial_def_example : Nat :=
  run_extended_cmd (ExtendedCmd.twice (ExtendedCmd.base (BaseCmd.tick (BaseCmd.halt 3))))

end PartialDefInheritance

end Lp2lc.Active
