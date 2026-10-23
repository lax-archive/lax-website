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

instance {V : Type u} (H : EdgeIndexedGraph V) : Fintype H.Edge :=
  H.edgeFintype

instance {V : Type u} (H : EdgeIndexedGraph V) : DecidableEq H.Edge :=
  H.edgeDecidableEq

/-- A named edge has exactly one endpoint in `S`. -/
def Crosses {V : Type u} [DecidableEq V]
    (H : EdgeIndexedGraph V) (S : Finset V) (e : H.Edge) : Prop :=
  (H.left e ∈ S ∧ H.right e ∉ S) ∨
    (H.right e ∈ S ∧ H.left e ∉ S)

/-- The named edge boundary of `S`. -/
noncomputable def boundary {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (S : Finset V) : Finset H.Edge :=
  @Finset.filter H.Edge (H.Crosses S) (Classical.decPred _) Finset.univ

/-- Boundary edges whose endpoints survive deletion of `removed`. -/
noncomputable def availableBoundary
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (removed S : Finset V) : Finset H.Edge :=
  (H.boundary S).filter fun e =>
    H.left e ∉ removed ∧ H.right e ∉ removed

namespace ElementCut

end ElementCut

/-- Every two distinct terminals need at least `k` nonterminal vertices and
edge copies to separate them. -/
def TerminalElementConnectedAtLeast
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (terminals : Finset V) (k : ℕ) : Prop :=
  ∀ ⦃a : V⦄, a ∈ terminals →
    ∀ ⦃b : V⦄, b ∈ terminals → a ≠ b →
      ∀ removed side : Finset V,
        Disjoint removed terminals →
        a ∈ side → b ∉ side → Disjoint side removed →
          k ≤ removed.card + (H.availableBoundary removed side).card

/-- Delete one named edge copy. -/
def deleteEdge {V : Type u} (H : EdgeIndexedGraph V) (e₀ : H.Edge) :
    EdgeIndexedGraph V where
  Edge := {e : H.Edge // e ≠ e₀}
  left e := H.left e.1
  right e := H.right e.1
  end_ne e := H.end_ne e.1

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

/-- Image of the terminal set under a contraction map. -/
def terminalImage {V : Type u} {W : Type v} [DecidableEq W]
    (mapVertex : V → W) (terminals : Finset V) : Finset W :=
  terminals.image mapVertex

namespace Path

end Path

end EdgeIndexedGraph

end Lax17.TerminalConnectivity
end

-- Lax17.HindOellermann
section
namespace Lax17.HindOellermann

universe u

/-- Hind--Oellermann deletion--contraction for terminal element
connectivity. -/
axiom hindOellermannDeletionContraction :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V)
    (terminals : Finset V) (k : ℕ) (e₀ : H.Edge),
      H.left e₀ ∉ terminals → H.right e₀ ∉ terminals →
        H.TerminalElementConnectedAtLeast terminals k →
          (H.deleteEdge e₀).TerminalElementConnectedAtLeast terminals k ∨
            ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
              (K : Lax17.TerminalConnectivity.EdgeIndexedGraph W)
              (mapVertex : V → W),
                Nonempty (H.IsContraction e₀ K mapVertex) ∧
                  K.TerminalElementConnectedAtLeast
                    (Lax17.TerminalConnectivity.EdgeIndexedGraph.terminalImage
                      mapVertex terminals) k

end Lax17.HindOellermann
end
