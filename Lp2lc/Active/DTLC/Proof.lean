import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.DTLC.Def

namespace Lp2lc.Active

namespace DTLC

namespace Trm

open Util

/-- Erasing annotations always produces a type-erased term. -/
theorem eraseType_isErased (I : Index) : ∀ (self : Trm I), self.typeEraseAll.TypeIsErased
| .val (.primitive _) _ => rfl
| .val (.fn body _) _ =>
  ⟨rfl, rfl, fun arg => eraseType_isErased I (body arg)⟩
| .apply fn arg _ =>
  ⟨rfl, eraseType_isErased I fn, eraseType_isErased I arg⟩
| .ref _ _ => rfl

end Trm

end DTLC
