-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Powerset
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

-- Lax342547.FractionalColoring
section
namespace Lax342547.FractionalColoring

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

structure Coloring (G : SimpleGraph V) where
  weight : Finset V → ℝ
  nonneg : ∀ S, 0 ≤ weight S
  supported : ∀ (S : Finset V), ¬ G.IsIndepSet (S : Set V) → weight S = 0
  covers : ∀ v, 1 ≤ ∑ S : Finset V, if v ∈ S then weight S else 0

noncomputable def totalWeight {G : SimpleGraph V} (C : Coloring G) : ℝ :=
  ∑ S : Finset V, C.weight S

noncomputable def fractionalChromaticNumber (G : SimpleGraph V) : ℝ :=
  sInf {w : ℝ | ∃ C : Coloring G, totalWeight C = w}

end Lax342547.FractionalColoring
end

-- Lax342547.FractionalCounterexample
section
namespace Lax342547.FractionalCounterexample

open CliqueMinor FractionalColoring

axiom arbitrarily_large_fractional_counterexample (lowerBound : ℕ) :
    ∃ m : ℕ, lowerBound ≤ m ∧ 5 ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧
      (hadwigerNumber G : ℝ) < 26 * (m : ℝ) / 75 + 2 / 3 ∧
      26 * (m : ℝ) / 75 + 2 / 3 < (m : ℝ) / 2 ∧
      (m : ℝ) / 2 ≤ fractionalChromaticNumber G ∧
      fractionalChromaticNumber G ≤ (G.chromaticNumber.toNat : ℝ)

end Lax342547.FractionalCounterexample
end
