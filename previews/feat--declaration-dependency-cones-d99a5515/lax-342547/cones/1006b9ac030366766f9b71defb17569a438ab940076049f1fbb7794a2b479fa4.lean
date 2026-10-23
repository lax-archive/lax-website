-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.HoleRelation
section
namespace Lax342547
end Lax342547

namespace Lax342547.HoleRelation
end Lax342547.HoleRelation

namespace Lax342547.HoleRelation.HoleData
end Lax342547.HoleRelation.HoleData
end

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.GradientForm
section
namespace Lax342547.GradientForm
end Lax342547.GradientForm
end

-- Lax342547.CutProfiles
section
namespace Lax342547.CutProfiles
end Lax342547.CutProfiles
end

-- Lax342547.TagGeometry
section
namespace Lax342547.TagGeometry
end Lax342547.TagGeometry

namespace Lax342547.TagGeometry.allowedBase
end Lax342547.TagGeometry.allowedBase

namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase
end

-- Lax342547.ConcreteGeometry
section
namespace Lax342547.ConcreteGeometry
end Lax342547.ConcreteGeometry

namespace Lax342547.ConcreteGeometry.changeZ
end Lax342547.ConcreteGeometry.changeZ
end

-- Lax342547.AtomDirections
section
namespace Lax342547.AtomDirections
end Lax342547.AtomDirections
end

-- Lax342547.FiniteLinearLaw
section
namespace Lax342547.FiniteLinearLaw
end Lax342547.FiniteLinearLaw
end

-- Lax342547.LowRankCounting
section
namespace Lax342547.LowRankCounting
end Lax342547.LowRankCounting
end

-- Lax342547.SharpMixerLaw
section
namespace Lax342547.SharpMixerLaw

variable {K A I N P : Type} [Field K] [Fintype A]

def alternatingBlock (c : N → I) (d : P → I) : Matrix I I K →ₗ[K] Matrix N P K where
  toFun M i j := M (c i) (d j) + M (d j) (c i)
  map_add' M L := by
    ext i j
    change (M (c i) (d j) + L (c i) (d j)) + (M (d j) (c i) + L (d j) (c i)) =
      (M (c i) (d j) + M (d j) (c i)) + (L (c i) (d j) + L (d j) (c i))
    exact add_add_add_comm _ _ _ _
  map_smul' a M := by
    ext i j
    change a * M (c i) (d j) + a * M (d j) (c i) = a * (M (c i) (d j) + M (d j) (c i))
    exact (mul_add _ _ _).symm

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.AtomDirections

open scoped ENNReal

axiom alternating_block_uniform {I N P : Type} [Fintype I] [Fintype N] [Fintype P]
    [DecidableEq I] [DecidableEq N] [DecidableEq P]
    (c : N → I) (d : P → I) (hc : Function.Injective c) (hd : Function.Injective d)
    (hcd : ∀ i j, c i ≠ d j) :
    (PMF.uniformOfFintype (Matrix I I Binary)).map (alternatingBlock c d) =
      PMF.uniformOfFintype (Matrix N P Binary)

end Lax342547.SharpMixerLaw
end
