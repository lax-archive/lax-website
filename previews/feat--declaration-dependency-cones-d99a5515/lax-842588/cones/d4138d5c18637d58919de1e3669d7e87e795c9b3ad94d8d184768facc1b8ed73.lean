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

/-- Finite terms over a ranked alphabet. A node labelled by `a` has one
ordered child for each element of `Fin (A.rank a)`. -/
inductive Tree (A : RankedAlphabet.{u}) : Type u
  | node (a : A.Symbol) (children : Fin (A.rank a) → Tree A) : Tree A

namespace ChildIndex

end ChildIndex

namespace Node

end Node

/-- A language of ranked trees. -/
abbrev TreeLanguage (A : RankedAlphabet.{u}) := Set (Tree A)

end Lax842588.RankedTree
end

-- Lax842588.TreeAutomaton
section
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

/-- The language accepted by a tree automaton. -/
def language {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q) :
    TreeLanguage A :=
  {t | M.Accepts t}

end Automaton

end Lax842588.TreeAutomaton
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

/-- A finite ranked alphabet is described by listing the ranks of its symbols.
The symbol in position `i` has rank `code[i]`. -/
abbrev RankedAlphabetCode := List Nat

namespace RankedAlphabetCode

/-- The canonical ranked alphabet represented by a rank string. -/
def toRankedAlphabet (code : RankedAlphabetCode) : RankedAlphabet where
  Symbol := Fin code.length
  symbolsFintype := inferInstance
  symbolsDecidableEq := inferInstance
  rank i := code.get i

end RankedAlphabetCode

/-- A finite transition consists of a symbol number, a parent-state number,
and the ordered list of child-state numbers. -/
abbrev TransitionCode := Nat × Nat × List Nat

/-- An automaton body consists of its number of states, transition list, and
accepting-state list. Its ranked alphabet is supplied separately. -/
abbrev AutomatonCode := Nat × List TransitionCode × List Nat

namespace AutomatonCode

/-- The tree automaton denoted by an automaton body over an encoded
ranked alphabet. Out-of-range states and malformed transitions are ignored. -/
def toAutomaton (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    Automaton alphabet.toRankedAlphabet (Fin M.1) where
  transition a q childStates :=
    M.2.1.any fun tr =>
      decide (tr.1 = a.val ∧ tr.2.1 = q.val ∧
        tr.2.2 = List.ofFn (fun i => (childStates i).val))
  accept q := M.2.2.contains q.val

/-- The ranked-tree language denoted by an automaton body over an encoded
ranked alphabet. -/
def language (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    TreeLanguage alphabet.toRankedAlphabet :=
  (M.toAutomaton alphabet).language

end AutomatonCode

end Lax842588.ValueTranslations
end
