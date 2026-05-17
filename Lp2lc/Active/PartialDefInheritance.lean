namespace Lp2lc.Active

namespace PartialDefInheritance

/-- Base command syntax used to demonstrate inheritance by embedding a smaller language. -/
inductive BaseCmd where
  | halt : Nat → BaseCmd
  | tick : BaseCmd → BaseCmd

def runBaseCmd : BaseCmd → Nat
  | .halt n => n
  | .tick next => runBaseCmd next + 1

/-- Extended command syntax that embeds base commands and adds a second operation. -/
inductive ExtendedCmd where
  | base : BaseCmd → ExtendedCmd
  | twice : ExtendedCmd → ExtendedCmd

def runExtendedCmd : ExtendedCmd → Nat
  | .base cmd => runBaseCmd cmd
  | .twice cmd => runExtendedCmd cmd * 2

def inheritedPartialDefExample : Nat :=
  runExtendedCmd (ExtendedCmd.twice (ExtendedCmd.base (BaseCmd.tick (BaseCmd.halt 3))))

end PartialDefInheritance

end Lp2lc.Active
