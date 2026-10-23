-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.Graph.Simple

-- Lax683916.MultigraphIsomorphism
section
namespace Lax683916.MultigraphIsomorphism

/-- An incidence-preserving vertex-and-edge isomorphism from a multigraph to a simple graph. -/
structure IsomorphicToSimpleGraph {α β V : Type*} (G : Graph α β) (H : SimpleGraph V) where
  /-- The bijection between the actual vertices of the two graphs. -/
  vertexEquiv : G.vertexSet ≃ V
  /-- The bijection between the actual edges of the two graphs. -/
  edgeEquiv : G.edgeSet ≃ H.edgeSet
  /-- The vertex and edge bijections preserve the endpoint relation. -/
  map_isLink : ∀ (e : G.edgeSet) (u v : G.vertexSet),
    G.IsLink e.1 u.1 v.1 ↔
      (edgeEquiv e).1 = s(vertexEquiv u, vertexEquiv v)

end Lax683916.MultigraphIsomorphism
end

-- Lax683916.MultigraphRepresentation
section
namespace Lax683916.MultigraphRepresentation

open Lax683916.MultigraphIsomorphism

universe u v

/-- Every simple multigraph is isomorphic to a simple graph on its actual vertex set. -/
axiom exists_simpleGraph_representation {α : Type u} {β : Type v}
    (G : Graph α β) [G.Simple] :
  ∃ H : SimpleGraph G.vertexSet, Nonempty (IsomorphicToSimpleGraph G H)

end Lax683916.MultigraphRepresentation
end
