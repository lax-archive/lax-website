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

instance {V : Type u} (H : EdgeIndexedGraph V) : DecidableEq H.Edge :=
  H.edgeDecidableEq

namespace ElementCut

end ElementCut

/-- A simple path in an edge-indexed multigraph. -/
structure Path {V : Type u} [DecidableEq V]
    (H : EdgeIndexedGraph V) (source target : V) where
  length : ℕ
  vertex : Fin (length + 1) → V
  edge : Fin length → H.Edge
  source_eq : vertex 0 = source
  target_eq : vertex (Fin.last length) = target
  edge_ends :
    ∀ i : Fin length,
      (H.left (edge i) = vertex i.castSucc ∧
        H.right (edge i) = vertex i.succ) ∨
      (H.right (edge i) = vertex i.castSucc ∧
        H.left (edge i) = vertex i.succ)
  vertex_injective : Function.Injective vertex

namespace Path

/-- The named edge copies used by an edge-indexed path. -/
def edgeSet
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V}
    {source target : V} (P : Path H source target) : Finset H.Edge :=
  Finset.univ.image P.edge

end Path

end EdgeIndexedGraph

end Lax17.TerminalConnectivity
end
