-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

-- Lax18.EdgeDensity
section
namespace Lax18.EdgeDensity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The number of adjacent ordered pairs from `A` to `B`. -/
noncomputable def edgeCountBetween (G : SimpleGraph V)
    (A B : Finset V) : ℕ := by
  classical
  exact ((A.product B).filter fun p : V × V => G.Adj p.1 p.2).card

/-- The real-valued edge density between two vertex sets. -/
noncomputable def density (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  if A.card = 0 ∨ B.card = 0 then
    0
  else
    (edgeCountBetween G A B : ℝ) / ((A.card : ℝ) * (B.card : ℝ))

end Lax18.EdgeDensity
end
