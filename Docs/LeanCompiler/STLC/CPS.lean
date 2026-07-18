import «LeanCompiler».STLC.Source

namespace LeanCompiler.STLC.CPS

inductive PType : Type where
  | bool : PType
  | cont : PType → PType
  | unit : PType
  | prod : PType → PType → PType
  deriving DecidableEq, Repr

@[simp] def PType.denote : PType → Type
  | .bool => Bool
  | .cont t => PType.denote t → Bool
  | .unit => PUnit
  | .prod t1 t2 => PType.denote t1 × PType.denote t2

mutual
  inductive PTerm (var : PType → Type) (result : PType) : Type where
    | halt : var result → PTerm var result
    | app : var (.cont t) → var t → PTerm var result
    | bind : PPrimop var result t → (var t → PTerm var result) → PTerm var result

  inductive PPrimop (var : PType → Type) (result : PType) : PType → Type where
    | var : var t → PPrimop var result t
    | tru : PPrimop var result .bool
    | fals : PPrimop var result .bool
    | abs : (var t → PTerm var result) → PPrimop var result (.cont t)
    | pair : var t1 → var t2 → PPrimop var result (.prod t1 t2)
    | fst : var (.prod t1 t2) → PPrimop var result t1
    | snd : var (.prod t1 t2) → PPrimop var result t2
end

abbrev PTermClosed (result : PType) := (var : PType → Type) → PTerm var result
abbrev PPrimopClosed (result t : PType) := (var : PType → Type) → PPrimop var result t

mutual
  @[simp] def PTerm.denote {result : PType} :
      PTerm PType.denote result → (PType.denote result → Bool) → Bool
    | .halt v, k => k v
    | .app f x, _ => f x
    | .bind p e, k => PTerm.denote (e (PPrimop.denote p k)) k

  @[simp] def PPrimop.denote {result t : PType} :
      PPrimop PType.denote result t → (PType.denote result → Bool) → PType.denote t
    | .var v, _ => v
    | .tru, _ => true
    | .fals, _ => false
    | .abs e, k => λ x => PTerm.denote (e x) k
    | .pair v1 v2, _ => (v1, v2)
    | .fst v, _ => v.1
    | .snd v, _ => v.2
end

@[simp] def PTermClosed.denote {result : PType} (e : PTermClosed result) :
    (PType.denote result → Bool) → Bool :=
  PTerm.denote (e PType.denote)

@[simp] def PPrimopClosed.denote {result t : PType} (p : PPrimopClosed result t) :
    (PType.denote result → Bool) → PType.denote t :=
  PPrimop.denote (p PType.denote)

structure VarPair (var1 var2 : PType → Type) where
  t : PType
  v1 : var1 t
  v2 : var2 t

abbrev Ctxt (var1 var2 : PType → Type) : Type := List (VarPair var1 var2)

@[simp] def mkPair {var1 var2 : PType → Type} {t : PType} (v1 : var1 t) (v2 : var2 t) :
    VarPair var1 var2 :=
  ⟨t, v1, v2⟩

mutual
  inductive PTermEquiv {result : PType} {var1 var2 : PType → Type} :
      Ctxt var1 var2 → PTerm var1 result → PTerm var2 result → Prop where
    | halt {G} {v1 : var1 result} {v2 : var2 result} :
        mkPair v1 v2 ∈ G →
        PTermEquiv G (.halt v1) (.halt v2)
    | app {G t} {f1 : var1 (.cont t)} {f2 : var2 (.cont t)} {x1 : var1 t} {x2 : var2 t} :
        mkPair f1 f2 ∈ G →
        mkPair x1 x2 ∈ G →
        PTermEquiv G (.app f1 x1) (.app f2 x2)
    | bind {G t} {p1 : PPrimop var1 result t} {p2 : PPrimop var2 result t}
        {e1 : var1 t → PTerm var1 result} {e2 : var2 t → PTerm var2 result} :
        PPrimopEquiv (result := result) G p1 p2 →
        (∀ v1 v2, PTermEquiv (mkPair v1 v2 :: G) (e1 v1) (e2 v2)) →
        PTermEquiv G (.bind p1 e1) (.bind p2 e2)

  inductive PPrimopEquiv {result : PType} {var1 var2 : PType → Type} :
      Ctxt var1 var2 → {t : PType} → PPrimop var1 result t → PPrimop var2 result t → Prop where
    | var {G t} {v1 : var1 t} {v2 : var2 t} :
        mkPair v1 v2 ∈ G →
        PPrimopEquiv G (.var v1) (.var v2)
    | tru {G} :
        PPrimopEquiv (result := result) G (.tru (var := var1)) (.tru (var := var2))
    | fals {G} :
        PPrimopEquiv (result := result) G (.fals (var := var1)) (.fals (var := var2))
    | pair {G t1 t2} {x1 : var1 t1} {x2 : var2 t1} {y1 : var1 t2} {y2 : var2 t2} :
        mkPair x1 x2 ∈ G →
        mkPair y1 y2 ∈ G →
        PPrimopEquiv G (.pair x1 y1) (.pair x2 y2)
    | fst {G t1 t2} {x1 : var1 (.prod t1 t2)} {x2 : var2 (.prod t1 t2)} :
        mkPair x1 x2 ∈ G →
        PPrimopEquiv G (.fst x1) (.fst x2)
    | snd {G t1 t2} {x1 : var1 (.prod t1 t2)} {x2 : var2 (.prod t1 t2)} :
        mkPair x1 x2 ∈ G →
        PPrimopEquiv G (.snd x1) (.snd x2)
    | abs {G t} {f1 : var1 t → PTerm var1 result} {f2 : var2 t → PTerm var2 result} :
        (∀ v1 v2, PTermEquiv (mkPair v1 v2 :: G) (f1 v1) (f2 v2)) →
        PPrimopEquiv G (.abs f1) (.abs f2)
end

class PTermParametricity : Prop where
  closed :
    ∀ {result : PType} (E : PTermClosed result) (var1 var2 : PType → Type),
      PTermEquiv ([] : Ctxt var1 var2) (E var1) (E var2)

theorem ptermEquivClosed [PTermParametricity] :
  ∀ {result : PType} (E : PTermClosed result) (var1 var2 : PType → Type),
    PTermEquiv ([] : Ctxt var1 var2) (E var1) (E var2) :=
  PTermParametricity.closed

end LeanCompiler.STLC.CPS
