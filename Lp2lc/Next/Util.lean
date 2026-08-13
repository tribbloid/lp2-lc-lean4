import «Lp2lc».Active.Util

namespace Lp2lc.Next.Util

open Lp2lc.Active.Util

/--
Receipt-indexed bridge between values and identifiers.

The value family is indexed by this bridge's evidence so recursive PHOAS
carriers can retain the receipt required by `get`.
-/
class UIdEquiv (UId : TIndex) (V : HasEv UId → Type) extends HasEv UId where
  inv : (value : V toHasEv) → toHasEv.Receipt
  get : (receipt : toHasEv.Receipt) → V toHasEv
  rightInv : ∀ (value : V toHasEv), get (inv value) = value
  leftInv : ∀ (receipt : toHasEv.Receipt), inv (get receipt) = receipt

/-
TODO: Avoid fake construction through UIdEquiv

the above code allow the same type of UId to be generated from different instances, this has caused serious problem in the constructive proof as it allow fake V to be created.

I'd like to plug this loophole:

- UIdEquiv should be a subclass of `HasEv` (similar to Aux)
- `inv` should return `Ev UId`, get should consume it
- other functions should adapt
- AST in type system definitions are mostly intact
  - but when being used in BuildEnv and ExeEnv, their original Carrier will no longer be able to carry the receipts of `trm2valCtx`/`trm2TypCtx`
  - therefore, new carriers defined by `F.WithEv` have to be used instead:
    - `CVar` := Carrier for trm2valCtx
    - `CTyp` := Carrier for trm2typCtx
    - `Trm.eval` accepts `Trm CVar` and produce `Trm CVar`
    - `Trm.infer` accepts `Trm CVar` and produce `Typ CTyp`, since some `Trm CVar` may contain `.ref` to free variables assigned `trm2valCtx`, the new `BuildEnv` will need access to both `trm2valCtx` and `trm2TypCtx` to work properly

This is a large-scale migration, you should gradually migrate existing code to a new directory/package `Lp2lc/Next`, in multiple steps & git commits.

- For a component, definition and implementation/discharge should be migrated in 2 different commits
- After each commit, you must ask for permission before proceeding to the next step

The following code are strictly prohibited, every commit should be followed by a subagent that warn against such violations:

- duplicated definition (e.g. duplicated inductive cases in multiple definitions)
- leaky abstraction & unnecessary copy & paste
- moving/weakening goalpost (e.g. adding axiom, modifying theorem signature)
- bloated code after migration
- introducing new/exotic concept that doesn't exist in original code

Resolution in this module: identifiers are consumed only through evidence-bearing
receipts, and the value family retains the evidence used by its PHOAS carrier.
-/

namespace UIdEquiv

abbrev Receipt {UId : TIndex} {V : HasEv UId → Type}
    (self : UIdEquiv UId V) :=
  self.toHasEv.Receipt

/-- Attaches independently witnessed metadata to receipts from one outer bridge. -/
class Aux {UId : TIndex} {V : HasEv UId → Type}
    (outer : UIdEquiv UId V) (M : V outer.toHasEv → Sort u)
    extends HasEv outer.Receipt where
  inv : (bundle : PSigma M) → Ev (outer.inv bundle.fst)
  get : (receipt : toHasEv.Receipt) → M (outer.get receipt.fst)
end UIdEquiv

namespace Free

abbrev Fixpoint (self : Free) (V : Free → Type) :=
  UIdEquiv self.Carrier
    (λ evidence => V ({} : self.WithEv evidence).toFree)

end Free

end Lp2lc.Next.Util
