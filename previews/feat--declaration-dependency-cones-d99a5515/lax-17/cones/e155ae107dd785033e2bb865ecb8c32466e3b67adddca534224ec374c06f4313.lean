-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Sum

-- Lax17.TerminalConnectivity
section
namespace Lax17.TerminalConnectivity.EdgeIndexedGraph.ElementLinkage
end Lax17.TerminalConnectivity.EdgeIndexedGraph.ElementLinkage

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

namespace ElementCut

end ElementCut

/-- A concrete model of contracting `e₀`.  The vertex map has precisely the
contracted endpoint pair as its only nontrivial fibre, and the target edges
are exactly the surviving non-loop edge copies. -/
structure IsContraction
    {V : Type u} {W : Type v} [DecidableEq W]
    (H : EdgeIndexedGraph V) (e₀ : H.Edge)
    (K : EdgeIndexedGraph W) (mapVertex : V → W) where
  vertex_surjective : Function.Surjective mapVertex
  endpoints_identified :
    mapVertex (H.left e₀) = mapVertex (H.right e₀)
  fibres :
    ∀ ⦃x y : V⦄, mapVertex x = mapVertex y →
      x = y ∨
        (x = H.left e₀ ∧ y = H.right e₀) ∨
        (x = H.right e₀ ∧ y = H.left e₀)
  edgeEquiv :
    {e : H.Edge //
      e ≠ e₀ ∧ mapVertex (H.left e) ≠ mapVertex (H.right e)} ≃ K.Edge
  edge_endpoints :
    ∀ e,
      (K.left (edgeEquiv e) = mapVertex (H.left e.1) ∧
        K.right (edgeEquiv e) = mapVertex (H.right e.1)) ∨
      (K.left (edgeEquiv e) = mapVertex (H.right e.1) ∧
        K.right (edgeEquiv e) = mapVertex (H.left e.1))

namespace Path

end Path

end EdgeIndexedGraph

end Lax17.TerminalConnectivity
end
