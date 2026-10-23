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

/-- The five-cycle. -/
abbrev C5 : SimpleGraph (Fin 5) := SimpleGraph.cycleGraph 5

/-- A graph has no induced copy of the five-cycle. -/
def IsC5Free {V : Type u} (G : SimpleGraph V) : Prop :=
  ¬ C5 ⊴ G

/-- The largest cardinality of a clique or stable set in a finite graph. -/
noncomputable def homogeneousNumber {V : Type u} (G : SimpleGraph V) : ℕ :=
  max G.cliqueNum G.indepNum

end Lax54.GraphDefinitions
end

-- Lax54.ErdosHajnalC5
section
namespace Lax54.ErdosHajnalC5

open Lax54.GraphDefinitions

universe u

/-- The Erdős–Hajnal property for the five-cycle, in integer-exponent form. -/
axiom erdos_hajnal_C5 :
    ∃ q : ℕ, 0 < q ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsC5Free G → Fintype.card V ≤ homogeneousNumber G ^ q

end Lax54.ErdosHajnalC5
end
