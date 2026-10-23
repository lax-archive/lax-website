-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Hasse

-- Lax54.GraphDefinitions
section
namespace Lax54.GraphDefinitions.StableHubComb
end Lax54.GraphDefinitions.StableHubComb

open Finset

open scoped SimpleGraph

namespace Lax54.GraphDefinitions

universe u

/-- The largest cardinality of a clique or stable set in a finite graph. -/
noncomputable def homogeneousNumber {V : Type u} (G : SimpleGraph V) : ℕ :=
  max G.cliqueNum G.indepNum

end Lax54.GraphDefinitions
end

-- Lax57.GraphDefinitions
section
namespace Lax57.GraphDefinitions.Blockade
end Lax57.GraphDefinitions.Blockade

open Finset

open scoped SimpleGraph

namespace Lax57.GraphDefinitions

universe u

/-- The path on five vertices. -/
abbrev P5 : SimpleGraph (Fin 5) := SimpleGraph.pathGraph 5

/-- A graph has no induced copy of the five-vertex path. -/
def IsP5Free {V : Type u} (G : SimpleGraph V) : Prop :=
  ¬ P5 ⊴ G

/-- The largest cardinality of a clique or stable set. -/
noncomputable abbrev homogeneousNumber {V : Type u} (G : SimpleGraph V) : ℕ :=
  Lax54.GraphDefinitions.homogeneousNumber G

end Lax57.GraphDefinitions
end

-- Lax57.ErdosHajnalP5
section
namespace Lax57.ErdosHajnalP5

open Lax57.GraphDefinitions

universe u

/-- The Erdős–Hajnal conjecture for the five-vertex path. -/
axiom erdos_hajnal_P5 :
    ∃ q : ℕ, 0 < q ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsP5Free G → Fintype.card V ≤ homogeneousNumber G ^ q

end Lax57.ErdosHajnalP5
end
