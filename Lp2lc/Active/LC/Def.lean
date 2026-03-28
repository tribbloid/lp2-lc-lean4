import Mathlib.Tactic
import «Lp2lc».Active.Shared
import «Lp2lc».Util

namespace Lp2lc.Active


namespace LC -- untyped lambda calculus

inductive AST(F: Rep) : Rep
| bvar : Nat -> AST F .trm -- de Bruijn for bounded variable (TODO: marked for removal in PHOAS version)
| fvar : Var -> AST F .trm -- name for free variable (they also have de Bruijn but are quite useless)
| fn : (I: F .typ) -> (out: F .trm) -> AST F .trm -- {x: I => out}, out may contain x
| app : (fn: F .trm) -> (x: F .trm) -> AST F .trm -- {fn(x)}
| anyT : AST F .typ -- can bind anything, in type system without subtyping (e.g. LEAN, Haskell) this is usually an internal feature, user cannot declare it

def Trm (F: Rep) := AST F .trm
def Typ (F: Rep) := AST F .typ

def EnvTrms (F: Rep) := Finset (Var × AST F .trm)
def EnvTyps (F: Rep) := Finset (Var × AST F .typ)
def Env (F: Rep) := EnvTrms F × EnvTyps F

def typing (F: Rep) : Env F -> (x: Trm F) -> (T: Typ F) -> Prop -- true if x can inhabit T
 := sorry

def isValue : Trm F -> Prop
  := sorry

def canReduce : Trm F -> Trm F -> Prop
  := sorry


def preservation : Prop := ∀ (F: Rep) (E : Env F) (e e' : Trm F) (T : Typ F),
  typing F E e T ->
  canReduce e e' ->
  typing F E e' T

-- def progress : Prop := ∀ (F: Rep) (E: Env F) (e : Trm F) (T : Typ F),
--   Typing E e T ->
--   Value e ∨ (∃ e', Red e e')



end LC

end Lp2lc.Active
