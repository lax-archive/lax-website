-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fintype.Basic
import Mathlib.ModelTheory.Semantics

-- Lax52.MSOSyntax
section
namespace Lax52
end Lax52

namespace Lax52.MSOSyntax
end Lax52.MSOSyntax

namespace Lax52.MSOSyntax.Formula
end Lax52.MSOSyntax.Formula

namespace Lax52.MSOSyntax.Formula.equal
end Lax52.MSOSyntax.Formula.equal

namespace Lax52.MSOSyntax.Formula.exFO
end Lax52.MSOSyntax.Formula.exFO

namespace Lax52.MSOSyntax.Formula.exSO
end Lax52.MSOSyntax.Formula.exSO

namespace Lax52.MSOSyntax.Formula.falsum
end Lax52.MSOSyntax.Formula.falsum

namespace Lax52.MSOSyntax.Formula.mem
end Lax52.MSOSyntax.Formula.mem

namespace Lax52.MSOSyntax.Formula.neg
end Lax52.MSOSyntax.Formula.neg

namespace Lax52.MSOSyntax.Formula.or
end Lax52.MSOSyntax.Formula.or

namespace Lax52.MSOSyntax.Formula.rel
end Lax52.MSOSyntax.Formula.rel
end

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

/-- A language of ranked trees. -/
abbrev TreeLanguage (A : RankedAlphabet.{u}) := Set (Tree A)

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

/-- The language accepted by a tree automaton. -/
def language {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q) :
    TreeLanguage A :=
  {t | M.Accepts t}

end Automaton

end Lax53.TreeAutomaton
end

-- Lax52.MSOSemantics
section
namespace Lax52.MSOSemantics
end Lax52.MSOSemantics

namespace Lax52.MSOSemantics.Realize
end Lax52.MSOSemantics.Realize
end

-- Lax53.TreeStructure
section
namespace Lax53.TreeStructure
end Lax53.TreeStructure

namespace Lax53.TreeStructure.TreeRelation
end Lax53.TreeStructure.TreeRelation

namespace Lax53.TreeStructure.treeStructure
end Lax53.TreeStructure.treeStructure

namespace Lax53.TreeStructure.TreeRelation.child
end Lax53.TreeStructure.TreeRelation.child

namespace Lax53.TreeStructure.TreeRelation.label
end Lax53.TreeStructure.TreeRelation.label
end

-- Lax53.ValueTranslations
section
namespace Lax53.ValueTranslations

open Lax52.MSOSyntax

open Lax53.RankedTree

open Lax53.TreeStructure

open Lax53.TreeAutomaton

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

end Lax53.ValueTranslations
end
