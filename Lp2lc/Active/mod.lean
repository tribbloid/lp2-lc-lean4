
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.Parameters
import «Lp2lc».Active.NatBindings
import «Lp2lc».Active.PartialDefInheritance

-- gDOT, higher-kinded gDOT, and DSub syntax.
import «Lp2lc».Active.GDOT.GDOTDef
import «Lp2lc».Active.HKGDOT.HKGDOTDef
import «Lp2lc».Active.DSub.DSubDef
import «Lp2lc».Active.DSub.Serial.Def
import «Lp2lc».Active.DSub.Serial.Infra

-- STLC syntax, hashing, serial execution, and type inference.
import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.Serial.Def
import «Lp2lc».Active.STLC.Serial.Infra
import «Lp2lc».Active.STLC.Hash
import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.Serial.Infer
import «Lp2lc».Active.STLC.Serial.__Infer_proof
import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer

-- Fuel-bounded semantic typing and expected-type checking.
import «Lp2lc».Active.STLC.Serial.__SemType
import «Lp2lc».Active.STLC.Serial.__SemType_proof

-- UId receipt execution and type inference.
import «Lp2lc».Active.STLC.UId.Def
import «Lp2lc».Active.STLC.UId.Infra
import «Lp2lc».Active.STLC.UId.Eval
import «Lp2lc».Active.STLC.UId.Infer
import «Lp2lc».Active.STLC.UId.__Infer_proof

-- Self-contained certified STLC evaluation (machine-generated).
import «Lp2lc».Active.STLC_minimal.mod

-- import «Lp2lc».Active.DOT.DOTDef
