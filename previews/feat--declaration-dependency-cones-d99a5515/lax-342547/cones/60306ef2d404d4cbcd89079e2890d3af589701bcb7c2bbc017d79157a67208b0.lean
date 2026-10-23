-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Lattice.Nat

-- Lax342547.CliqueMinor
section
namespace Lax342547.CliqueMinor

def HasCliqueMinor {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V,
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w)

noncomputable def hadwigerNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {t : ℕ | HasCliqueMinor G t}

end Lax342547.CliqueMinor
end

-- Lax342547.ConnectedMatching
section
namespace Lax342547
end Lax342547

namespace Lax342547.ConnectedMatching
end Lax342547.ConnectedMatching
end

-- Lax342547.Counterexample
section
namespace Lax342547.Counterexample

open ConnectedMatching CliqueMinor

/-- The ordinary coloring consequence of Theorem 1.1. -/
axiom arbitrarily_large_hadwiger_counterexample (lowerBound : ℕ) :
    ∃ m : ℕ, lowerBound ≤ m ∧ 5 ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧ hadwigerNumber G < G.chromaticNumber.toNat

end Lax342547.Counterexample
end
