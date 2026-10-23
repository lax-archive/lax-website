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
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.DeriveFintype

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

-- Lax342547.RawFrames
section
namespace Lax342547.RawFrames
end Lax342547.RawFrames

namespace Lax342547.RawFrames.Frame
end Lax342547.RawFrames.Frame
end

-- Lax342547.ConcreteCut
section
namespace Lax342547.ConcreteCut
end Lax342547.ConcreteCut

namespace Lax342547.ConcreteCut.Testers
end Lax342547.ConcreteCut.Testers
end

-- Lax342547.Atoms
section
namespace Lax342547.Atoms
end Lax342547.Atoms

namespace Lax342547.Atoms.Flavor
end Lax342547.Atoms.Flavor

namespace Lax342547.Atoms.retained
end Lax342547.Atoms.retained

namespace Lax342547.Atoms.testerSummary
end Lax342547.Atoms.testerSummary

namespace Lax342547.Atoms.Flavor.generic
end Lax342547.Atoms.Flavor.generic

namespace Lax342547.Atoms.Flavor.pure
end Lax342547.Atoms.Flavor.pure

namespace Lax342547.Atoms.Flavor.sharedOnly
end Lax342547.Atoms.Flavor.sharedOnly
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

-- Lax342547.OrderedMixerLaw
section
namespace Lax342547.OrderedMixerLaw
end Lax342547.OrderedMixerLaw
end

-- Lax342547.SharpMixerLaw
section
namespace Lax342547.SharpMixerLaw

variable {K A I N P : Type} [Field K] [Fintype A]

def weighted (c : A → K) : (A → Matrix I I K) →ₗ[K] Matrix I I K where
  toFun M := ∑ a, c a • M a
  map_add' M L := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' r M := by simp [smul_smul, Finset.smul_sum, mul_comm]

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.AtomDirections

open scoped ENNReal

end Lax342547.SharpMixerLaw
end

-- Lax342547.BinaryMixer
section
namespace Lax342547.BinaryMixer
end Lax342547.BinaryMixer
end

-- Lax342547.BinaryMixers
section
namespace Lax342547.BinaryMixers

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.Atoms Lax342547.AtomDirections Lax342547.BinaryMixer

def SharpGood {n b : ℕ} (M : Fin b → Matrix (Fin n) (Fin n) Binary) : Prop :=
  ∀ s t : Fin b → Binary, s ≠ t → ∀ c d : Binary, (c ≠ 0 ∨ d ≠ 0) →
    n ≤ 5 * (c • SharpMixerLaw.weighted (fun a => s a + t a) M +
      d • (SharpMixerLaw.weighted (fun a => s a + t a) M).transpose).rank

open scoped ENNReal

end Lax342547.BinaryMixers
end
