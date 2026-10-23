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
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
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
namespace Lax342547.TagGeometry.allowedBase
end Lax342547.TagGeometry.allowedBase

namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase

namespace Lax342547.TagGeometry

open Lax342547.MomentSpace

abbrev Tag (k : ℕ) := ZMod (2 * k + 1)

def interval (k : ℕ) (d : Tag k) : Finset (Tag k) :=
  Finset.univ.image (fun i : Fin k => d + (i.val + 1 : ℕ))

abbrev Base (k n : ℕ) := ((Tag k × Tag k) × Fin n) ⊕ (Fin 3 × Fin n)

end Lax342547.TagGeometry
end

-- Lax342547.ConcreteGeometry
section
namespace Lax342547.ConcreteGeometry.changeZ
end Lax342547.ConcreteGeometry.changeZ

namespace Lax342547.ConcreteGeometry

open Lax342547.MomentSpace Lax342547.TagGeometry

def ordinary {k n : ℕ} (d t : Tag k) (i : Fin n) : Base k n := Sum.inl ((d, t), i)

def shared {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (0, i)

def pairLeft {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val, by omega⟩

def pairRight {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val + 1, by omega⟩

end Lax342547.ConcreteGeometry
end

-- Lax342547.FiniteLinearLaw
section
namespace Lax342547.FiniteLinearLaw
end Lax342547.FiniteLinearLaw
end

-- Lax342547.AffineImages
section
namespace Lax342547.AffineImages
end Lax342547.AffineImages
end

-- Lax342547.GramColumns
section
namespace Lax342547.GramColumns
end Lax342547.GramColumns
end

-- Lax342547.GramNormalization
section
namespace Lax342547.GramNormalization
end Lax342547.GramNormalization
end

-- Lax342547.AffineSliceIndependence
section
namespace Lax342547.AffineSliceIndependence
end Lax342547.AffineSliceIndependence

namespace Lax342547.AffineSliceIndependence.affineColumns
end Lax342547.AffineSliceIndependence.affineColumns

namespace Lax342547.AffineSliceIndependence.eraseFree
end Lax342547.AffineSliceIndependence.eraseFree

namespace Lax342547.AffineSliceIndependence.joinedFree
end Lax342547.AffineSliceIndependence.joinedFree

namespace Lax342547.AffineSliceIndependence.pointColumns
end Lax342547.AffineSliceIndependence.pointColumns
end

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
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

-- Lax342547.RealCellLaws
section
namespace Lax342547.RealCellLaws
end Lax342547.RealCellLaws
end

-- Lax342547.ConditionedAffineColumns
section
namespace Lax342547.ConditionedAffineColumns
end Lax342547.ConditionedAffineColumns
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

-- Lax342547.EmpiricalVariance
section
namespace Lax342547.EmpiricalVariance
end Lax342547.EmpiricalVariance
end

-- Lax342547.RawFrames
section
namespace Lax342547.RawFrames
end Lax342547.RawFrames

namespace Lax342547.RawFrames.Frame
end Lax342547.RawFrames.Frame
end

-- Lax342547.RawLaw
section
namespace Lax342547.RawLaw
end Lax342547.RawLaw
end

-- Lax342547.FrameSymmetry
section
namespace Lax342547.FrameSymmetry
end Lax342547.FrameSymmetry

namespace Lax342547.FrameSymmetry.Change
end Lax342547.FrameSymmetry.Change
end

-- Lax342547.FrameTuples
section
namespace Lax342547.FrameTuples
end Lax342547.FrameTuples
end

-- Lax342547.JoinedGramOrbits
section
namespace Lax342547.JoinedGramOrbits
end Lax342547.JoinedGramOrbits
end

-- Lax342547.FourierTests
section
namespace Lax342547.FourierTests
end Lax342547.FourierTests
end

-- Lax342547.ConditionedMixing
section
namespace Lax342547.ConditionedMixing
end Lax342547.ConditionedMixing
end

-- Lax342547.BilinearWalsh
section
namespace Lax342547.BilinearWalsh
end Lax342547.BilinearWalsh
end

-- Lax342547.SlotWalsh
section
namespace Lax342547.SlotWalsh
end Lax342547.SlotWalsh
end

-- Lax342547.CrossBatchMixing
section
namespace Lax342547.CrossBatchMixing
end Lax342547.CrossBatchMixing
end

-- Lax342547.CrossGramBasis
section
namespace Lax342547.CrossGramBasis
end Lax342547.CrossGramBasis

namespace Lax342547.CrossGramBasis.tests
end Lax342547.CrossGramBasis.tests
end

-- Lax342547.GramOrbitDensity
section
namespace Lax342547.GramOrbitDensity
end Lax342547.GramOrbitDensity

namespace Lax342547.GramOrbitDensity.batchEquiv
end Lax342547.GramOrbitDensity.batchEquiv
end

-- Lax342547.JointGramInjection
section
namespace Lax342547.JointGramInjection
end Lax342547.JointGramInjection

namespace Lax342547.JointGramInjection.ambientEquiv
end Lax342547.JointGramInjection.ambientEquiv
end

-- Lax342547.RawBatchComparison
section
namespace Lax342547.RawBatchComparison
end Lax342547.RawBatchComparison

namespace Lax342547.RawBatchComparison.target
end Lax342547.RawBatchComparison.target
end

-- Lax342547.RawFrameComparison
section
namespace Lax342547.RawFrameComparison
end Lax342547.RawFrameComparison
end

-- Lax342547.GroupTensorComparison
section
namespace Lax342547.GroupTensorComparison
end Lax342547.GroupTensorComparison
end

-- Lax342547.RawGroupedComparison
section
namespace Lax342547.RawGroupedComparison
end Lax342547.RawGroupedComparison
end

-- Lax342547.AffineSliceVariance
section
namespace Lax342547.AffineSliceVariance
end Lax342547.AffineSliceVariance
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
namespace Lax342547.Atoms.retained
end Lax342547.Atoms.retained

namespace Lax342547.Atoms.testerSummary
end Lax342547.Atoms.testerSummary

namespace Lax342547.Atoms

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.ConcreteCut

inductive Flavor (k : ℕ) where
  | generic
  | sharedOnly
  | pure (blocks : Finset (Tag k × Tag k))
  deriving Fintype

end Lax342547.Atoms
end

-- Lax342547.FlavorAffineSlices
section
namespace Lax342547.FlavorAffineSlices
end Lax342547.FlavorAffineSlices
end

-- Lax342547.FixedSelectorGram
section
namespace Lax342547.FixedSelectorGram

noncomputable section

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.AffineSliceIndependence Lax342547.FlavorAffineSlices Lax342547.Atoms

open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

abbrev TesterBlock (k : ℕ) := Option (Tag k × Tag k)

def testerCoordinate {k n r : ℕ} (hr : 2*r ≤ n)
    (u : TesterBlock k × Fin r × Bool) : Base k n :=
  let i := if u.2.2 then pairRight hr u.2.1 else pairLeft hr u.2.1
  match u.1 with
  | none => shared i
  | some (d,t) => ordinary d t i

def blockRetained {k : ℕ} (l : Tag k) (f : Flavor k) : TesterBlock k → Prop
  | none => match f with | .pure _ => False | _ => True
  | some (d,t) => l ∈ interval k d ∧ match f with
      | .generic => True | .sharedOnly => False | .pure blocks => (d,t) ∈ blocks

abbrev Slots {k : ℕ} (l : Tag k) (f : Flavor k) (r : ℕ) :=
  {q : TesterBlock k // blockRetained l f q} × Fin r × Bool

noncomputable instance {k : ℕ} (l : Tag k) (f : Flavor k) :
    Fintype {q : TesterBlock k // blockRetained l f q} := Fintype.ofFinite _

def restrictedGram {k r : ℕ} {l : Tag k} {f : Flavor k} {D : Type}
    (X : Matrix (Slots l f r) (Option D) Binary) : Matrix (Option D) (Option D) Binary :=
  fun i j => ∑ q : {q : TesterBlock k // blockRetained l f q},∑ ρ : Fin r,
    X (q,ρ,false) i*X (q,ρ,true) j

end

end Lax342547.FixedSelectorGram
end
