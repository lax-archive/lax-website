-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Basic
import Mathlib.ModelTheory.Semantics

-- Lax146103.MSOSyntax
section
namespace Lax146103
end Lax146103

namespace Lax146103.MSOSyntax
end Lax146103.MSOSyntax

namespace Lax146103.MSOSyntax.Formula
end Lax146103.MSOSyntax.Formula

namespace Lax146103.MSOSyntax.Formula.equal
end Lax146103.MSOSyntax.Formula.equal

namespace Lax146103.MSOSyntax.Formula.exFO
end Lax146103.MSOSyntax.Formula.exFO

namespace Lax146103.MSOSyntax.Formula.exSO
end Lax146103.MSOSyntax.Formula.exSO

namespace Lax146103.MSOSyntax.Formula.falsum
end Lax146103.MSOSyntax.Formula.falsum

namespace Lax146103.MSOSyntax.Formula.mem
end Lax146103.MSOSyntax.Formula.mem

namespace Lax146103.MSOSyntax.Formula.neg
end Lax146103.MSOSyntax.Formula.neg

namespace Lax146103.MSOSyntax.Formula.or
end Lax146103.MSOSyntax.Formula.or

namespace Lax146103.MSOSyntax.Formula.rel
end Lax146103.MSOSyntax.Formula.rel
end

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
namespace Lax842588.TreeAutomaton
end Lax842588.TreeAutomaton

namespace Lax842588.TreeAutomaton.Automaton
end Lax842588.TreeAutomaton.Automaton

namespace Lax842588.TreeAutomaton.Automaton.RunsTo
end Lax842588.TreeAutomaton.Automaton.RunsTo
end

-- Lax146103.MSOSemantics
section
namespace Lax146103.MSOSemantics
end Lax146103.MSOSemantics

namespace Lax146103.MSOSemantics.Realize
end Lax146103.MSOSemantics.Realize
end

-- Lax842588.TreeStructure
section
namespace Lax842588.TreeStructure
end Lax842588.TreeStructure

namespace Lax842588.TreeStructure.TreeRelation
end Lax842588.TreeStructure.TreeRelation

namespace Lax842588.TreeStructure.treeStructure
end Lax842588.TreeStructure.treeStructure

namespace Lax842588.TreeStructure.TreeRelation.child
end Lax842588.TreeStructure.TreeRelation.child

namespace Lax842588.TreeStructure.TreeRelation.label
end Lax842588.TreeStructure.TreeRelation.label
end

-- Lax842588.ValueTranslations
section
namespace Lax842588.ValueTranslations

open Lax146103.MSOSyntax

open Lax842588.RankedTree

open Lax842588.TreeStructure

open Lax842588.TreeAutomaton

namespace RankedAlphabetCode

end RankedAlphabetCode

/-- A finite transition consists of a symbol number, a parent-state number,
and the ordered list of child-state numbers. -/
abbrev TransitionCode := Nat × Nat × List Nat

/-- An automaton body consists of its number of states, transition list, and
accepting-state list. Its ranked alphabet is supplied separately. -/
abbrev AutomatonCode := Nat × List TransitionCode × List Nat

namespace AutomatonCode

end AutomatonCode

end Lax842588.ValueTranslations
end
