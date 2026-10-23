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

instance {V : Type u} (H : EdgeIndexedGraph V) : Fintype H.Edge :=
  H.edgeFintype

instance {V : Type u} (H : EdgeIndexedGraph V) : DecidableEq H.Edge :=
  H.edgeDecidableEq

namespace ElementCut

end ElementCut

/-- Delete one named edge copy. -/
def deleteEdge {V : Type u} (H : EdgeIndexedGraph V) (e₀ : H.Edge) :
    EdgeIndexedGraph V where
  Edge := {e : H.Edge // e ≠ e₀}
  left e := H.left e.1
  right e := H.right e.1
  end_ne e := H.end_ne e.1

namespace Path

end Path

end EdgeIndexedGraph

end Lax17.TerminalConnectivity
end
