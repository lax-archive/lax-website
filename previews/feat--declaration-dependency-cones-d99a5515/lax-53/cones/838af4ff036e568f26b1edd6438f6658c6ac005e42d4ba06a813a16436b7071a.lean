-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fintype.Basic

-- Lax53.RankedTree
section
namespace Lax53.RankedTree.Node.child
end Lax53.RankedTree.Node.child

namespace Lax53.RankedTree.Node.inChild
end Lax53.RankedTree.Node.inChild

namespace Lax53.RankedTree.Node.label
end Lax53.RankedTree.Node.label

namespace Lax53.RankedTree.Node.root
end Lax53.RankedTree.Node.root

namespace Lax53.RankedTree.Node.rootOf
end Lax53.RankedTree.Node.rootOf

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

namespace Node

end Node

end Lax53.RankedTree
end

-- Lax53.TreeAutomaton
section
namespace Lax53.TreeAutomaton

open Lax53.RankedTree

universe u v

/-- A bottom-up tree automaton with state type `Q`. This basic structure allows
arbitrary state types; recognizable languages and the main theorems explicitly
require finitely many states. -/
structure Automaton (A : RankedAlphabet.{u}) (Q : Type v) where
  transition : (a : A.Symbol) → Q → (Fin (A.rank a) → Q) → Bool
  accept : Q → Bool

namespace Automaton

/-- A run of `M` on `t` leading to state `q`. -/
def RunsTo {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q) :
    Tree A → Q → Prop
  | .node a children, q =>
      ∃ childStates : Fin (A.rank a) → Q,
        M.transition a q childStates = true ∧
          ∀ i : Fin (A.rank a), M.RunsTo (children i) (childStates i)

/-- A tree is accepted if some run leads to an accepting state. -/
def Accepts {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q)
    (t : Tree A) : Prop :=
  ∃ q : Q, M.accept q = true ∧ M.RunsTo t q

end Automaton

end Lax53.TreeAutomaton
end
