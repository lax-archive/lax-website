-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Powerset

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

axiom fractional_chromatic_lower_bound (G : SimpleGraph V) (hα : G.indepNum ≤ 2) :
    (Fintype.card V : ℝ) / 2 ≤ fractionalChromaticNumber G

end Lax342547.FractionalColoring
end
