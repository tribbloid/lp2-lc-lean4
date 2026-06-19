import LeanCompiler.STLC.Source
import LeanCompiler.STLC.CPS
import LeanCompiler.STLC.CC
import LeanCompiler.STLC.CPSify
import LeanCompiler.STLC.CCify

namespace LeanCompiler.STLC.Compile

open LeanCompiler.STLC.Source
open LeanCompiler.STLC.CPS
open LeanCompiler.STLC.CC
open LeanCompiler.STLC.CPSify
open LeanCompiler.STLC.CCify

@[simp] def compileTy (t : Ty) : CType :=
  .data (cpsType t)

@[simp] def compile [PTermParametricity] {t : Ty}
    (E : TermClosed t) : CProgClosed (cpsType t) :=
  CcTerm (CpsTerm E)

theorem compile_correct [TermParametricity] [PTermParametricity] (E : TermClosed .bool) :
    CProgClosed.denote (compile E) (fun b => b) = TermClosed.denote E := by
  unfold compile
  simpa using Eq.trans
    (CcTerm_correct (E := CpsTerm E) (k := fun b => b))
    (CpsTerm_correct_bool (E := E) (k := fun b => b))

end LeanCompiler.STLC.Compile
