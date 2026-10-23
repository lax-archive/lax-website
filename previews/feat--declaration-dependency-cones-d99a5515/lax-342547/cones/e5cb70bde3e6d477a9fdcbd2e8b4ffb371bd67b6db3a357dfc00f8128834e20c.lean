-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Floor.Ring
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

-- Lax342547.MetadataPins
section
namespace Lax342547.MetadataPins
end Lax342547.MetadataPins
end

-- Lax342547.SplitTrimming
section
namespace Lax342547.SplitTrimming
end Lax342547.SplitTrimming
end

-- Lax342547.SecondPeeling
section
namespace Lax342547.SecondPeeling

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.MetadataPins

open Lax342547.LeafPartition Lax342547.BoundedPeeling

open scoped ENNReal

noncomputable def supportFinset {Ω : Type} [Fintype Ω] (p : PMF Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun o => o ∈ p.support)

end Lax342547.SecondPeeling
end
