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

/-- Named edge copies incident with `x`. -/
def incidentEdges {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (x : V) : Finset H.Edge :=
  Finset.univ.filter fun e => H.left e = x ∨ H.right e = x

/-- A named edge has exactly one endpoint in `S`. -/
def Crosses {V : Type u} [DecidableEq V]
    (H : EdgeIndexedGraph V) (S : Finset V) (e : H.Edge) : Prop :=
  (H.left e ∈ S ∧ H.right e ∉ S) ∨
    (H.right e ∈ S ∧ H.left e ∉ S)

/-- The named edge boundary of `S`. -/
noncomputable def boundary {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (S : Finset V) : Finset H.Edge :=
  @Finset.filter H.Edge (H.Crosses S) (Classical.decPred _) Finset.univ

namespace ElementCut

end ElementCut

/-- A named edge is the whole boundary of some vertex set. -/
def IsNamedCutEdge {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (e : H.Edge) : Prop :=
  ∃ S : Finset V, H.boundary S = {e}

/-- No edge incident with `s` is a named cut edge. -/
def NoIncidentCutEdge {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (s : V) : Prop :=
  ∀ e ∈ H.incidentEdges s, ¬ H.IsNamedCutEdge e

namespace Path

end Path

end EdgeIndexedGraph

end Lax17.TerminalConnectivity
end
