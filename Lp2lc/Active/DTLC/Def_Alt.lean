
import «Lp2lc».Active.DTLC.Def

namespace Lp2lc.Active

namespace DTLC

/-- TODO: this is the same eval with function body evaluation, nto sure if it is needed -/
def Trm.eval2 {I : Index} [FBound I] (trm : Trm I) (fuel : Nat) : Option (Val I) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match trm with
    | .val (.fn body) =>
      some (.fn (body := fun arg =>
        let result := body arg
        match result.eval fuel with
        | some value => .val value
        | none => result))
    | .val value => some value
    | .depApply fn arg =>
      match fn.eval fuel, arg.eval fuel with
      | some (.fn body), some value => (body (FBound.fwd value)).eval fuel
      | _, _ => none

end DTLC

end Lp2lc.Active
