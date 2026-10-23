-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Sum

-- Lax17.TerminalConnectivity
section
namespace Lax17.TerminalConnectivity.EdgeIndexedGraph.ElementLinkage
end Lax17.TerminalConnectivity.EdgeIndexedGraph.ElementLinkage

namespace Lax17.TerminalConnectivity.EdgeIndexedGraph.IsContraction
end Lax17.TerminalConnectivity.EdgeIndexedGraph.IsContraction

namespace Lax17.TerminalConnectivity.EdgeIndexedGraph.splitOff
end Lax17.TerminalConnectivity.EdgeIndexedGraph.splitOff

namespace Lax17.TerminalConnectivity

universe u v

/-- A finite loopless undirected multigraph with named edge copies. -/
structure EdgeIndexedGraph (V : Type u) where
  Edge : Type
  [edgeFintype : Fintype Edge]
  [edgeDecidableEq : DecidableEq Edge]
  left : Edge → V
  right : Edge → V
  end_ne : ∀ e : Edge, left e ≠ right e

namespace EdgeIndexedGraph

namespace ElementCut

end ElementCut

/-- Two distinct named edges incident with `s`, with their other endpoints. -/
structure SplitPair {V : Type u} (H : EdgeIndexedGraph V) (s : V) where
  first : H.Edge
  second : H.Edge
  edge_ne : first ≠ second
  firstOther : V
  secondOther : V
  first_ends :
    (H.left first = s ∧ H.right first = firstOther) ∨
      (H.right first = s ∧ H.left first = firstOther)
  second_ends :
    (H.left second = s ∧ H.right second = secondOther) ∨
      (H.right second = s ∧ H.left second = secondOther)

/-- Edge names surviving or created by a split-off.  The right summand is
inhabited exactly when the newly created edge is not a loop. -/
def SplitEdge
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V} {s : V}
    (p : H.SplitPair s) : Type :=
  {e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕
    {_unit : Unit // p.firstOther ≠ p.secondOther}

noncomputable instance splitEdgeDecidableEq
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V} {s : V}
    (p : H.SplitPair s) : DecidableEq (SplitEdge p) :=
  Classical.decEq (SplitEdge p)

namespace Path

end Path

end EdgeIndexedGraph

end Lax17.TerminalConnectivity
end
