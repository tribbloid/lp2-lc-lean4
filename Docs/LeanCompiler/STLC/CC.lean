import «LeanCompiler».STLC.CPS

namespace LeanCompiler.STLC.CC

open LeanCompiler.STLC.CPS

inductive CType : Type where
  | data : PType → CType
  | code : PType → PType → CType
  deriving DecidableEq, Repr

inductive CPrimop (var : CType → Type) : CType → Type where
  | var : var (.data t) → CPrimop var (.data t)
  | tru : CPrimop var (.data .bool)
  | fals : CPrimop var (.data .bool)
  | pack : var (.code env arg) → var (.data env) → CPrimop var (.data (.cont arg))
  | unitIntro : CPrimop var (.data .unit)
  | pair : var (.data t1) → var (.data t2) → CPrimop var (.data (.prod t1 t2))
  | fst : var (.data (.prod t1 t2)) → CPrimop var (.data t1)
  | snd : var (.data (.prod t1 t2)) → CPrimop var (.data t2)

inductive CTerm (var : CType → Type) (result : PType) : Type where
  | halt : var (.data result) → CTerm var result
  | app : var (.data (.cont t)) → var (.data t) → CTerm var result
  | bind : CPrimop var ty → (var ty → CTerm var result) → CTerm var result

inductive CFuncs (var : CType → Type) (result : PType) (α : Type) : Type where
  | main : α → CFuncs var result α
  | abs :
      (var (.data env) → var (.data arg) → CTerm var result) →
      (var (.code env arg) → CFuncs var result α) →
      CFuncs var result α

abbrev CProg (var : CType → Type) (result : PType) : Type :=
  CFuncs var result (CTerm var result)

@[simp] def CType.denote : CType → Type
  | .data t => PType.denote t
  | .code env arg => PType.denote env → PType.denote arg → Bool

@[simp] def CPrimop.denote {t : CType} : CPrimop CType.denote t → CType.denote t
  | .var v => v
  | .tru => true
  | .fals => false
  | .pack f env => f env
  | .unitIntro => PUnit.unit
  | .pair v1 v2 => (v1, v2)
  | .fst v => v.1
  | .snd v => v.2

@[simp] def CTerm.denote {result : PType} :
    CTerm CType.denote result → (PType.denote result → Bool) → Bool
  | .halt v, k => k v
  | .app f x, _ => f x
  | .bind p e, k => CTerm.denote (e (CPrimop.denote p)) k

@[simp] def CFuncs.denote {result : PType} {α : Type} :
    CFuncs CType.denote result α → (PType.denote result → Bool) → α
  | .main v, _ => v
  | .abs e fs, k =>
      CFuncs.denote (fs (fun env arg => CTerm.denote (e env arg) k)) k

@[simp] def CProg.denote {result : PType} (p : CProg CType.denote result)
    (k : PType.denote result → Bool) : Bool :=
  CTerm.denote (CFuncs.denote p k) k

abbrev CPrimopClosed (t : CType) := (var : CType → Type) → CPrimop var t
abbrev CTermClosed (result : PType) := (var : CType → Type) → CTerm var result
abbrev CProgClosed (result : PType) := (var : CType → Type) → CProg var result

@[simp] def CPrimopClosed.denote {t : CType} (p : CPrimopClosed t) : CType.denote t :=
  CPrimop.denote (p CType.denote)

@[simp] def CTermClosed.denote {result : PType} (e : CTermClosed result) :
    (PType.denote result → Bool) → Bool :=
  CTerm.denote (e CType.denote)

@[simp] def CProgClosed.denote {result : PType} (p : CProgClosed result) :
    (PType.denote result → Bool) → Bool :=
  CProg.denote (p CType.denote)

end LeanCompiler.STLC.CC
