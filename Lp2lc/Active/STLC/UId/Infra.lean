import «Lp2lc».Active.STLC.UId.Def

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace Root
variable {this : Root}

-- File-private structural view; consume the construction callback only at `.inr ()`.
@[match_pattern] private abbrev bind := @Pre.Binder.mk

/-- Resolves an ancestor reference into the current carrier before shared receipt lookup. -/
def mapRef {source P : Parameters} (under : source.Under P) (carrier : source.TRef)
    (encoding : P.I = .FreeOrUnit := by rfl) : P.TRef := by
  cases under with
  | same => exact carrier
  | @lower p2 prev =>
    have recurse := mapRef prev carrier encoding
    rcases p2 with ⟨⟨B⟩, I, index⟩
    cases encoding
    exact .inl recurse

/-- Changes an AST's reference carrier while retaining its bytecode type and index encoding.

Opens source callbacks only at `.inr ()` and maps their fixed bodies using `Sum.map map id`.
The rebuilt callbacks return the mapped body for every input. Preserving the right `Unit` summand
keeps the newest slots available for later substitution and makes a backward carrier map unnecessary.
The local visitor keeps the shared syntax indices general for structural recursion.
-/
@[simp] def AST.recarrier {I l} (self : this.AST l) (map : this.UId → I) : (⟨I⟩ : Root).AST l :=
  visit self rfl map
where
  visit {P l I} (self : Pre.AST P l) (encoding : P.I = .FreeOrUnit)
      (map : P.TRef → I) : Pre.AST {P with I := .FreeOrUnit, index := I} l :=
    match self with
    | .TLit => .TLit
    | .TFn tIn tOut => .TFn (visit tIn encoding map) (visit tOut encoding map)
    | .lit repr => .lit repr
    | .fn tIn (bind body) => by
      have input := visit tIn encoding map
      have recurse := λ {I} carrier => visit (I := I) (body carrier)
      rcases P with ⟨B, _, _⟩
      cases encoding
      exact .fn input (.mk (λ _ => recurse (.inr ()) rfl (Sum.map map id)))
    | .val value => .val (visit value encoding map)
    | .apply fnTerm arg => .apply (visit fnTerm encoding map) (visit arg encoding map)
    | .ref carrier under => .ref (map (mapRef under carrier encoding)) .same

/-- Instantiates a UId binder by substituting a receipt into its canonical structural body.

After opening only at `.inr ()`, the reference map sends `.inl outer` to `outer` and `.inr ()` to
`carrier`, returning syntax in the original context. Beneath nested binders, carrier transport
preserves their newest slots while substituting references to this outer slot.

Use `Root.Binder.apply` to instantiate UId syntax. Its call to the shared raw `Pre.Binder.apply`
supplies `.inr ()` solely to obtain the body in the extended context.
-/
def Binder.apply {l} (self : this.Binder l) (carrier : this.UId) :=
  AST.recarrier (Pre.Binder.apply self (.inr ())) (Sum.elim id (λ _ => carrier))

/-- Values in the image of structural normalization, with unused callback inputs erased. -/
abbrev CanonicalVal (this : Root) :=
  {value : this.Val // ∃ source : this.Val, AST.recarrier source id = value}

/-- Admits a raw value by normalizing its canonical binder bodies. -/
def canonicalVal (value : this.Val) : this.CanonicalVal :=
  ⟨AST.recarrier value id, value, rfl⟩

abbrev TypOrVal (this : Root) := this.Typ ⊕ this.CanonicalVal

end Root

/-- One read-only receipt view shared by compile-time type lookup and runtime value lookup. -/
structure UIdRefs extends base : Root where
  uid2both : KVRefs UId base.TypOrVal

/-- Compile-time minting accepts types or canonical values without requiring an executable environment. -/
class BuildEnv (refs : UIdRefs) where
  uid2bothCtx : KVEquiv refs.uid2both

/-- Runtime minting certifies shared lookup of the requested canonical structural value. -/
class ExeEnv (refs : UIdRefs) where
  uid2val (value : refs.base.CanonicalVal) :
    {receipt : refs.UId // refs.uid2both.get receipt = .inr value}

instance {refs} [build : BuildEnv refs] : ExeEnv refs where
  uid2val value := ⟨build.uid2bothCtx.inv (.inr value), build.uid2bothCtx.rightInv _⟩

end Lp2lc.Active.STLC
