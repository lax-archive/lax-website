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

-- Lax683916.SimpleGraphMultigraphRepresentation
section
namespace Lax683916.SimpleGraphMultigraphRepresentation

open Lax683916.MultigraphIsomorphism

universe u

/-- Every simple graph is represented by a simple multigraph on its vertices. -/
axiom exists_multigraph_representation {V : Type u} (H : SimpleGraph V) :
  ∃ G : Graph V (Sym2 V), G.Simple ∧ Nonempty (IsomorphicToSimpleGraph G H)

end Lax683916.SimpleGraphMultigraphRepresentation
end
