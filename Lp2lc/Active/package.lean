
-- STLC module exports Def and Example
import «Lp2lc».Active.STLC.Proof
import «Lp2lc».Active.STLC.Example
import «Lp2lc».Active.SysF.Def
import «Lp2lc».Active.SysF.Proof
import «Lp2lc».Active.SysF.Example
import «Lp2lc».Active.SysFSub.Def
import «Lp2lc».Active.SysFSub.Proof
import «Lp2lc».Active.SysFSub.Example
import «Lp2lc».Active.SysFOmega.Def
import «Lp2lc».Active.SysFOmega.Proof
import «Lp2lc».Active.SysFOmega.Example


  def type_function_example : Type → Type :=
    fun α => α

  def poly_example: Type 1 :=
    (α : Type) -> (α → α)
