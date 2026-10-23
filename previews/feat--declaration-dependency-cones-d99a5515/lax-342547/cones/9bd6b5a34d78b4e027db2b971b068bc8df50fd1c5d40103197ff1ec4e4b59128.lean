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
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.DeriveFintype
import Mathlib.Topology.Instances.Real.Lemmas

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

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

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

open Lax342547.MomentSpace

def Component (Tag : Type) := {e : Finset Tag // e.card = 2}

variable {Tag V : Type} [AddCommGroup V] [Module Binary V]

end Lax342547.CutProfiles
end

-- Lax342547.TagGeometry
section
namespace Lax342547.TagGeometry.allowedBase
end Lax342547.TagGeometry.allowedBase

namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase

namespace Lax342547.TagGeometry

open Lax342547.MomentSpace

abbrev Tag (k : ℕ) := ZMod (2 * k + 1)

abbrev Base (k n : ℕ) := ((Tag k × Tag k) × Fin n) ⊕ (Fin 3 × Fin n)

end Lax342547.TagGeometry
end

-- Lax342547.ConcreteGeometry
section
namespace Lax342547.ConcreteGeometry.changeZ
end Lax342547.ConcreteGeometry.changeZ

namespace Lax342547.ConcreteGeometry

open Lax342547.MomentSpace Lax342547.TagGeometry

abbrev Coordinate (k n b degree : ℕ) := SelectorCoordinates b degree × Option (Base k n)

abbrev Moment (k n b degree : ℕ) := Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary

end Lax342547.ConcreteGeometry
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

-- Lax342547.CommonAtoms
section
namespace Lax342547.CommonAtoms
end Lax342547.CommonAtoms
end

-- Lax342547.BaseMoments
section
namespace Lax342547.BaseMoments
end Lax342547.BaseMoments
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

-- Lax342547.SelectorInterpolation
section
namespace Lax342547.SelectorInterpolation
end Lax342547.SelectorInterpolation
end

-- Lax342547.BooleanWeight
section
namespace Lax342547.BooleanWeight
end Lax342547.BooleanWeight
end

-- Lax342547.QuadraticDegree
section
namespace Lax342547.QuadraticDegree
end Lax342547.QuadraticDegree
end

-- Lax342547.PointQuadratics
section
namespace Lax342547.PointQuadratics
end Lax342547.PointQuadratics
end

-- Lax342547.AtomFunctionals
section
namespace Lax342547.AtomFunctionals

open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut

open Lax342547.ConcreteGeometry Lax342547.CutProfiles Lax342547.SelectorInterpolation

open scoped BigOperators

noncomputable def starMatrixMap {k n b degree : ℕ} (l : Tag k) :
    Moment k n b degree →ₗ[Binary] (Component (Tag k) → Moment k n b degree) := by
  classical
  exact { toFun := fun M e => if l ∈ e.val then M else 0
          map_add' := by intro x y; funext e; by_cases h : l ∈ e.val <;> simp [h]
          map_smul' := by intro c x; funext e; by_cases h : l ∈ e.val <;> simp [h] }

end Lax342547.AtomFunctionals
end
