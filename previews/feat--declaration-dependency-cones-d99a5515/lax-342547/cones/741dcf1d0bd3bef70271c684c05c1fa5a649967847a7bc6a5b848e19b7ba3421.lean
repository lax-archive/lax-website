-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
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

-- Lax342547.LeafExtraction
section
namespace Lax342547.LeafExtraction
end Lax342547.LeafExtraction
end

-- Lax342547.LeafPartition
section
namespace Lax342547.LeafPartition
end Lax342547.LeafPartition
end

-- Lax342547.PeelingBudget
section
namespace Lax342547
end Lax342547

namespace Lax342547.PeelingBudget
end Lax342547.PeelingBudget
end

-- Lax342547.BoundedPeeling
section
namespace Lax342547.BoundedPeeling
end Lax342547.BoundedPeeling
end

-- Lax342547.LeafTrimming
section
namespace Lax342547.LeafTrimming
end Lax342547.LeafTrimming
end

-- Lax342547.RestrictedLeaves
section
namespace Lax342547.RestrictedLeaves

open Lax342547.MomentSpace Lax342547.ExactPins

open Lax342547.LeafTrimming Lax342547.BoundedPeeling

open scoped ENNReal

axiom weighted_residual {J : Type} [Fintype J] (w r : J → ℝ≥0∞) (δ : ℝ≥0∞)
    (hw : ∑ j, w j ≤ 1) (hr : ∀ j, r j ≤ δ) : ∑ j, w j * r j ≤ δ

end Lax342547.RestrictedLeaves
end
