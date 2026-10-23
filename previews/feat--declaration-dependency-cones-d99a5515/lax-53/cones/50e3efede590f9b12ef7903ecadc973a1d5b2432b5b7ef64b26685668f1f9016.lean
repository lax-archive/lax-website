-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fintype.Basic

-- Lax53.RankedTree
section
namespace Lax53.RankedTree

universe u

/-- A finite alphabet whose symbols have prescribed arities. -/
structure RankedAlphabet where
  Symbol : Type u
  [symbolsFintype : Fintype Symbol]
  [symbolsDecidableEq : DecidableEq Symbol]
  rank : Symbol → Nat

attribute [instance] RankedAlphabet.symbolsFintype

attribute [instance] RankedAlphabet.symbolsDecidableEq

/-- Finite terms over a ranked alphabet. A node labelled by `a` has one
ordered child for each element of `Fin (A.rank a)`. -/
inductive Tree (A : RankedAlphabet.{u}) : Type u
  | node (a : A.Symbol) (children : Fin (A.rank a) → Tree A) : Tree A

namespace ChildIndex

end ChildIndex

/-- The nodes occurring in a particular ranked tree. -/
inductive Node {A : RankedAlphabet.{u}} : Tree A → Type u
  | root {a : A.Symbol} {children : Fin (A.rank a) → Tree A} :
      Node (.node a children)
  | inChild {a : A.Symbol} {children : Fin (A.rank a) → Tree A}
      (i : Fin (A.rank a)) (p : Node (children i)) :
      Node (.node a children)

namespace Node

/-- The root node of a tree. -/
def rootOf {A : RankedAlphabet.{u}} : (t : Tree A) → Node t
  | .node _ _ => .root

/-- The symbol labelling a node. -/
def label {A : RankedAlphabet.{u}} : {t : Tree A} → Node t → A.Symbol
  | .node a _, .root => a
  | .node _ _, .inChild _ p => label p

/-- The `i`th child of a node, as a node of the same ambient tree. -/
def child {A : RankedAlphabet.{u}} :
    {t : Tree A} → (p : Node t) → Fin (A.rank p.label) → Node t
  | .node _ children, .root, i => .inChild i (rootOf (children i))
  | .node _ _, .inChild j p, i => .inChild j (child p i)

end Node

end Lax53.RankedTree
end
