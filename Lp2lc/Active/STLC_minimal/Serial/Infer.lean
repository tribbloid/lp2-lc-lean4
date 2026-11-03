import «Lp2lc».Active.STLC_minimal.Serial.Infra
namespace Lp2lc.Active.STLC_minimal
open Lp2lc.Active.Util

namespace AST
variable {P : Parameters}

local instance typLE : LE (Pre.AST P .typ) := ⟨Eq⟩

@[instance_reducible]
local instance typDecidableLE : DecidableLE (Pre.AST P .typ)
  | .TLit, .TLit => isTrue rfl
  | .TLit, .TFn _ _
  | .TFn _ _, .TLit => isFalse (λ equality => nomatch equality)
  | .TFn a b, .TFn c d =>
    @decidable_of_iff' _ _ (Pre.AST.TFn.injEq a b c d).to_iff
      (@instDecidableAnd _ _ (typDecidableLE a c) (typDecidableLE b d))

def infer {n} (self : Trm n) (bindings : CompilerBindings := .empty) : RecOpt Typ := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | _ + 1, .pure (.val (.lit _)) => .yield (some .TLit)
  | fuel + 1, .pure (.val (.fn tIn body)) =>
    (infer (body.apply .only)
      (bindings.set (n + 1) ⟨n, tIn, .empty⟩) fuel).map (Option.map (.TFn (resolveType tIn)))
  | fuel + 1, .pure (.ref _ under) =>
    match bindings under.sourceIndex.down with
    | some (.inl ⟨_, typ, _⟩) => .yield (some typ.resolveType)
    | some (.inr ⟨_, value, captured⟩) => infer value.asTrm captured fuel
    | none => .yield none
  | fuel + 1, .apply fn arg =>
    match infer fn bindings fuel, infer arg bindings fuel with
    | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
      .yield (if argTyp ≤ tIn then some tOut else none)
    | .yield _, .yield _ => .yield none
    | _, _ => .outOfFuel
  | _ + 1, .pure (.val (.fnPrimitive tOut _)) => .yield (some (.TFn .TLit (resolveType tOut)))

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ: Typ) :=
  self.infer bindings fuel = .yield (.some typ)

end AST
end Lp2lc.Active.STLC_minimal
