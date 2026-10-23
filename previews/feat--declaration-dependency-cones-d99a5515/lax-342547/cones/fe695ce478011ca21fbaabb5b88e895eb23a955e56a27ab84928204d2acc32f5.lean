-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Union
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
end

-- Lax342547.LeafTrimming
section
namespace Lax342547.LeafTrimming

open scoped ENNReal

noncomputable def discardedMass {J : Type} [Fintype J]
    (w q : J → ℝ≥0∞) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j, if q j < δ then w j * q j else 0

axiom weighted_discard {J : Type} [Fintype J] (w q : J → ℝ≥0∞)
    (δ : ℝ≥0∞) (hw : ∑ j, w j ≤ 1) : discardedMass w q δ ≤ δ

end Lax342547.LeafTrimming
end
