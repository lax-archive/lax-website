-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

-- Lax10.ThreeConnectedAndColorable
section
open Finset

namespace Lax10.ThreeConnectedAndColorable

universe u

variable {V : Type u}

/-- The induced graph obtained after deleting the vertices in $S$. -/
def deleteVertices (G : SimpleGraph V) (S : Finset V) :
    SimpleGraph {v : V // v ∉ S} :=
  G.induce {v : V | v ∉ S}

/-- The set $S$ separates two vertices that remain after its deletion. -/
def IsVertexSeparator (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ x y : {v : V // v ∉ S}, ¬ (deleteVertices G S).Reachable x y

end Lax10.ThreeConnectedAndColorable
end
