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

namespace Lax17.TerminalConnectivity.EdgeIndexedGraph.SplitPair
end Lax17.TerminalConnectivity.EdgeIndexedGraph.SplitPair

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

/-- A named edge has exactly one endpoint in `S`. -/
def Crosses {V : Type u} [DecidableEq V]
    (H : EdgeIndexedGraph V) (S : Finset V) (e : H.Edge) : Prop :=
  (H.left e ∈ S ∧ H.right e ∉ S) ∨
    (H.right e ∈ S ∧ H.left e ∉ S)

/-- A terminal-separating cut made from nonterminal vertices and named edge
copies. -/
structure ElementCut
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (terminals : Finset V) (a b : V) where
  removedVertices : Finset V
  removedVertices_nonterminal : Disjoint removedVertices terminals
  removedEdges : Finset H.Edge
  side : Finset V
  source_mem : a ∈ side
  target_not_mem : b ∉ side
  side_disjoint_removed : Disjoint side removedVertices
  crossing_removed :
    ∀ e : H.Edge,
      H.left e ∉ removedVertices →
        H.right e ∉ removedVertices →
          H.Crosses side e →
            e ∈ removedEdges

namespace ElementCut

end ElementCut

namespace Path

end Path

end EdgeIndexedGraph

end Lax17.TerminalConnectivity
end
