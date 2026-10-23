-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Set.Card

-- Lax899194.NetworkCreationGame
section
namespace Lax899194.NetworkCreationGame

/-- The other players to which player `i` purchases edges. -/
def Strategy (n : ℕ) (i : Fin n) := { S : Set (Fin n) // i ∉ S }

/-- A choice of strategy for every player. -/
abbrev Profile (n : ℕ) := (i : Fin n) → Strategy n i

/-- The undirected network formed by all purchased edges. -/
def graph {n : ℕ} (s : Profile n) : SimpleGraph (Fin n) where
  Adj i j := j ∈ (s i).val ∨ i ∈ (s j).val
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨fun i h => h.elim (s i).property (s i).property⟩

end Lax899194.NetworkCreationGame
end

-- Lax899194.PlayerCost
section
namespace Lax899194.PlayerCost

open Lax899194.NetworkCreationGame

open scoped BigOperators NNReal ENNReal

/-- Edge expenditure plus the sum of distances from player `i` to all players. -/
noncomputable def playerCost {n : ℕ} (α : ℝ≥0) (s : Profile n)
    (i : Fin n) : ℝ≥0∞ :=
  (α : ℝ≥0∞) * (s i).val.ncard +
    ∑ j : Fin n, ((graph s).edist i j).toENNReal

end Lax899194.PlayerCost
end

-- Lax899194.SocialCost
section
namespace Lax899194.SocialCost

open Lax899194.NetworkCreationGame Lax899194.PlayerCost

open scoped BigOperators NNReal ENNReal

/-- The sum of all players' individual costs, with distances counted in both directions. -/
noncomputable def socialCost {n : ℕ} (α : ℝ≥0) (s : Profile n) : ℝ≥0∞ :=
  ∑ i : Fin n, playerCost α s i

end Lax899194.SocialCost
end

-- Lax899194.InefficiencyRatio
section
namespace Lax899194.InefficiencyRatio

open Lax899194.NetworkCreationGame Lax899194.SocialCost

open scoped NNReal ENNReal

/-- The least social cost among all strategy profiles with `n` players. -/
noncomputable def optimalCost (n : ℕ) (α : ℝ≥0) : ℝ≥0∞ :=
  ⨅ s : Profile n, socialCost α s

/-- The social cost of a profile divided by the social optimum for the same game. -/
noncomputable def inefficiencyRatio {n : ℕ} (α : ℝ≥0) (s : Profile n) : ℝ≥0∞ :=
  socialCost α s / optimalCost n α

end Lax899194.InefficiencyRatio
end
