-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.SetTheory.Cardinal.Finite

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
end Lax342547.LeafTrimming
end

-- Lax342547.MomentSpace
section
namespace Lax342547
end Lax342547

namespace Lax342547.MomentSpace
end Lax342547.MomentSpace

namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval
end

-- Lax342547.ExactPins
section
namespace Lax342547.ExactPins
end Lax342547.ExactPins

namespace Lax342547.ExactPins.Pin
end Lax342547.ExactPins.Pin
end

-- Lax342547.MetadataPins
section
namespace Lax342547.MetadataPins
end Lax342547.MetadataPins
end

-- Lax342547.SplitTrimming
section
namespace Lax342547.SplitTrimming

open Lax342547.MomentSpace Lax342547.MetadataPins

open scoped ENNReal

axiom repinning_density {Ω : Type} (p μ : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support)
    (hT : ∃ o ∈ T, o ∈ (p.filter S hS).support)
    (D ζ : ℝ) (N K₁ u : ℕ) (hζ : ζ ≤ 1)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * N)) ≤ p.toOuterMeasure S)
    (hTbound : (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * N)) ≤ (p.filter S hS).toOuterMeasure T)
    (hp : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ ((D + K₁ + 1) * N) * μ o) :
    ∀ o, ((p.filter S hS).filter T hT) o ≤
      (2 : ℝ≥0∞) ^ ((D + K₁ + u + 5) * N) * μ o

end Lax342547.SplitTrimming
end
