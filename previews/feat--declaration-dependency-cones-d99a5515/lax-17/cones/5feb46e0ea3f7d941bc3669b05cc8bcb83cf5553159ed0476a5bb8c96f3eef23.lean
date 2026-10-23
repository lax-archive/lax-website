-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Sym

-- Lax17.Paths
section
namespace Lax17.Paths.EdgeCutPartition
end Lax17.Paths.EdgeCutPartition

namespace Lax17.Paths.EdgeLinkage
end Lax17.Paths.EdgeLinkage

namespace Lax17.Paths.VertexLinkage
end Lax17.Paths.VertexLinkage

namespace Lax17.Paths.VertexLinkage.BridgeBetween
end Lax17.Paths.VertexLinkage.BridgeBetween

namespace Lax17.Paths

universe u

namespace Path

end Path

/-- Edges of `G` with one endpoint in `X` and the other in `Y`. -/
noncomputable def edgeBoundary {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X Y : Finset V) : Finset (Sym2 V) :=
  @Finset.filter (Sym2 V)
    (fun e => e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y))
    (Classical.decPred fun e =>
      e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y))
    Finset.univ

end Lax17.Paths
end

-- Lax17.Linkedness
section
namespace Lax17.Linkedness

universe u

open Lax17.Paths

/-- Cut-based edge well-linkedness with parameter `numerator / denominator`.
Every partition of the whole vertex set cuts the corresponding fraction of
the smaller terminal side. -/
def ScaledEdgeWellLinked {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V)
    (numerator denominator : ℕ) : Prop :=
  0 < numerator ∧ numerator ≤ denominator ∧
    ∀ X Y : Finset V,
      X ∪ Y = Finset.univ → Disjoint X Y →
        numerator * min (X ∩ T).card (Y ∩ T).card ≤
          denominator * (edgeBoundary G X Y).card

end Lax17.Linkedness
end
