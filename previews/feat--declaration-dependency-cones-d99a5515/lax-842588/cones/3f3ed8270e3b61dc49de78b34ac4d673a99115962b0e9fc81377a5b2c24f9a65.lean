-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Basic

-- Lax842588.RankedTree
section
namespace Lax842588.RankedTree.Tree
end Lax842588.RankedTree.Tree

namespace Lax842588.RankedTree.Node.child
end Lax842588.RankedTree.Node.child

namespace Lax842588.RankedTree.Node.inChild
end Lax842588.RankedTree.Node.inChild

namespace Lax842588.RankedTree.Node.label
end Lax842588.RankedTree.Node.label

namespace Lax842588.RankedTree.Node.root
end Lax842588.RankedTree.Node.root

namespace Lax842588.RankedTree.Node.rootOf
end Lax842588.RankedTree.Node.rootOf

namespace Lax842588.RankedTree.Tree.node
end Lax842588.RankedTree.Tree.node

namespace Lax842588.RankedTree

universe u

/-- A finite alphabet whose symbols have prescribed arities. -/
structure RankedAlphabet where
  Symbol : Type u
  [symbolsFintype : Fintype Symbol]
  [symbolsDecidableEq : DecidableEq Symbol]
  rank : Symbol → Nat

attribute [instance] RankedAlphabet.symbolsFintype

attribute [instance] RankedAlphabet.symbolsDecidableEq

namespace ChildIndex

end ChildIndex

namespace Node

end Node

end Lax842588.RankedTree
end

-- Lax842588.TreeAutomaton
section
namespace Lax842588.TreeAutomaton.Automaton.RunsTo
end Lax842588.TreeAutomaton.Automaton.RunsTo

namespace Lax842588.TreeAutomaton

open Lax842588.RankedTree

universe u v

/-- A bottom-up tree automaton with state type `Q`. This basic structure allows
arbitrary state types; recognizable languages and the main theorems explicitly
require finitely many states. -/
structure Automaton (A : RankedAlphabet.{u}) (Q : Type v) where
  transition : (a : A.Symbol) → Q → (Fin (A.rank a) → Q) → Bool
  accept : Q → Bool

namespace Automaton

/-- A bottom-up tree automaton is deterministic when every symbol and ordered
tuple of child states has a unique resulting parent state. -/
def Deterministic {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q) : Prop :=
  ∀ (a : A.Symbol) (childStates : Fin (A.rank a) → Q),
    ∃! q : Q, M.transition a q childStates = true

end Automaton

end Lax842588.TreeAutomaton
end
