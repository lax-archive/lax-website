-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

-- Lax54.GraphDefinitions
section
namespace Lax54.GraphDefinitions.StableHubComb
end Lax54.GraphDefinitions.StableHubComb

open Finset

open scoped SimpleGraph

namespace Lax54.GraphDefinitions

universe u

/--
The low-density alternative in Rödl's theorem. Either the graph or its
complement has edge density at most `1/E`; the definition clears the
denominator.
-/
def HasSparseSide {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (E : ℕ) : Prop :=
  E * 2 * G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) ∨
    E * 2 * Gᶜ.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1)

end Lax54.GraphDefinitions
end
