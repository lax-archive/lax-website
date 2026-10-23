-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Set
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Instances.Real.Lemmas

-- Lax342547.MomentSpace
section
namespace Lax342547
end Lax342547

namespace Lax342547.MomentSpace
end Lax342547.MomentSpace

namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh
end Lax342547.Walsh
end

-- Lax342547.PushforwardWalsh
section
namespace Lax342547.PushforwardWalsh
end Lax342547.PushforwardWalsh
end

-- Lax342547.RetainedImages
section
namespace Lax342547.RetainedImages
end Lax342547.RetainedImages
end

-- Lax342547.RelativeEntropy
section
namespace Lax342547.RelativeEntropy
end Lax342547.RelativeEntropy
end

-- Lax342547.EntropyLines
section
namespace Lax342547.EntropyLines
end Lax342547.EntropyLines
end

-- Lax342547.EntropyProjection
section
namespace Lax342547.EntropyProjection
end Lax342547.EntropyProjection
end

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
end

-- Lax342547.RealCellLaws
section
namespace Lax342547.RealCellLaws
end Lax342547.RealCellLaws
end

-- Lax342547.PairRecovery
section
namespace Lax342547.PairRecovery
end Lax342547.PairRecovery
end

-- Lax342547.UnitLaws
section
namespace Lax342547.UnitLaws
end Lax342547.UnitLaws
end

-- Lax342547.ContainerLaws
section
namespace Lax342547.ContainerLaws
end Lax342547.ContainerLaws
end

-- Lax342547.FiniteSampling
section
namespace Lax342547.FiniteSampling
end Lax342547.FiniteSampling
end

-- Lax342547.CoordinateRestrictions
section
namespace Lax342547.CoordinateRestrictions
end Lax342547.CoordinateRestrictions
end

-- Lax342547.AdaptiveSampling
section
namespace Lax342547.AdaptiveSampling
end Lax342547.AdaptiveSampling
end

-- Lax342547.AdaptiveSets
section
namespace Lax342547.AdaptiveSets

open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages

open scoped BigOperators

noncomputable def disjointEmbedding {ι : Type} [DecidableEq ι] (E J : Finset ι)
    (h : Disjoint E J) : E ⊕ J ↪ ι :=
  { toFun := Sum.elim Subtype.val Subtype.val
    inj' := by
      intro x y hxy
      cases x with
      | inl e =>
        cases y with
        | inl e' => exact congrArg Sum.inl (Subtype.ext hxy)
        | inr j =>
          dsimp at hxy
          exact False.elim ((Finset.disjoint_left.mp h) e.property (hxy.symm ▸ j.property))
      | inr j =>
        cases y with
        | inl e =>
          dsimp at hxy
          exact False.elim ((Finset.disjoint_left.mp h) e.property (hxy ▸ j.property))
        | inr j' => exact congrArg Sum.inr (Subtype.ext hxy) }

end Lax342547.AdaptiveSets
end
