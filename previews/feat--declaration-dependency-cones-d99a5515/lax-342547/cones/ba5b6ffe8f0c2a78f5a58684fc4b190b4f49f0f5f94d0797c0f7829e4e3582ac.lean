-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.QuadraticForm.Prod
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
namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

instance (b degree : ℕ) : Fintype (SelectorCoordinates b degree) :=
  inferInstanceAs (Fintype {S : Finset (Fin b) // S.card ≤ degree})

def selectorEval {b degree : ℕ} (s : Fin b → Binary)
    (c : SelectorCoordinates b degree) : Binary := ∏ i ∈ c.val, s i

variable {Label Coord Base : Type}

def baseEval (z : Base → Binary) : Option Base → Binary
  | none => 1
  | some i => z i

def point (p : Label → Coord → Binary) (s : Label) (z : Base → Binary)
    (i : Coord × Option Base) : Binary := p s i.1 * baseEval z i.2

def pointMoment (p : Label → Coord → Binary) (s : Label) (z : Base → Binary) :
    Matrix (Coord × Option Base) (Coord × Option Base) Binary :=
  fun i j => point p s z i * point p s z j

def momentSpace (p : Label → Coord → Binary) (A : Set Base) :
    Submodule Binary (Matrix (Coord × Option Base) (Coord × Option Base) Binary) :=
  Submodule.span Binary {w | ∃ s z, (∀ i, i ∉ A → z i = 0) ∧ w = pointMoment p s z}

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

def cutMap : (Tag → V) →ₗ[Binary] (Component Tag → V) where
  toFun w e := ∑ t ∈ e.val, w t
  map_add' w v := by ext e; simp [Finset.sum_add_distrib]
  map_smul' c w := by ext e; simp [Finset.smul_sum]

def representatives (W : Tag → Submodule Binary V) : Submodule Binary (Tag → V) :=
  Submodule.pi Set.univ W

end Lax342547.CutProfiles
end

-- Lax342547.TagGeometry
section
namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase

namespace Lax342547.TagGeometry

open Lax342547.MomentSpace

abbrev Tag (k : ℕ) := ZMod (2 * k + 1)

def interval (k : ℕ) (d : Tag k) : Finset (Tag k) :=
  Finset.univ.image (fun i : Fin k => d + (i.val + 1 : ℕ))

abbrev Base (k n : ℕ) := ((Tag k × Tag k) × Fin n) ⊕ (Fin 3 × Fin n)

def allowedBase (k n : ℕ) (l : Tag k) : Set (Base k n)
  | Sum.inl ((d, _), _) => l ∈ interval k d
  | Sum.inr _ => True

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

-- Lax342547.CoordinateCounts
section
namespace Lax342547.CoordinateCounts
end Lax342547.CoordinateCounts
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
namespace Lax342547.ConcreteCut.Testers
end Lax342547.ConcreteCut.Testers

namespace Lax342547.ConcreteCut

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles

noncomputable instance (k : ℕ) : Fintype (Component (Tag k)) := by
  classical
  exact inferInstanceAs (Fintype {e : Finset (Tag k) // e.card = 2})

def tagSpace (k n b degree : ℕ) (l : Tag k) : Submodule Binary (Moment k n b degree) :=
  momentSpace selectorEval (allowedBase k n l)

abbrev Representation (k n b degree : ℕ) := representatives (tagSpace k n b degree)

def representationCut (k n b degree : ℕ) :
    Representation k n b degree →ₗ[Binary] (Component (Tag k) → Moment k n b degree) :=
  cutMap.comp (representatives (tagSpace k n b degree)).subtype

abbrev Profile (k n b degree : ℕ) := LinearMap.range (representationCut k n b degree)

end Lax342547.ConcreteCut
end

-- Lax342547.LowRankCounting
section
namespace Lax342547.LowRankCounting
end Lax342547.LowRankCounting
end

-- Lax342547.SymmetricFactorization
section
namespace Lax342547.SymmetricFactorization
end Lax342547.SymmetricFactorization
end

-- Lax342547.ProfileCounting
section
namespace Lax342547.ProfileCounting
end Lax342547.ProfileCounting
end

-- Lax342547.CorankCounting
section
namespace Lax342547.CorankCounting
end Lax342547.CorankCounting
end

-- Lax342547.FiniteLinearLaw
section
namespace Lax342547.FiniteLinearLaw
end Lax342547.FiniteLinearLaw
end

-- Lax342547.MixerCompatibility
section
namespace Lax342547
end Lax342547

namespace Lax342547.MixerCompatibility
end Lax342547.MixerCompatibility
end

-- Lax342547.MixerRowLaw
section
namespace Lax342547.MixerRowLaw
end Lax342547.MixerRowLaw
end

-- Lax342547.AtomDirections
section
namespace Lax342547.AtomDirections
end Lax342547.AtomDirections
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

-- Lax342547.FormalQuadratic
section
namespace Lax342547.FormalQuadratic
end Lax342547.FormalQuadratic
end

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.UnaryMixer
section
namespace Lax342547.UnaryMixer
end Lax342547.UnaryMixer

namespace Lax342547.UnaryMixer.blockRank
end Lax342547.UnaryMixer.blockRank
end

-- Lax342547.UnaryRowLaw
section
namespace Lax342547.UnaryRowLaw
end Lax342547.UnaryRowLaw

namespace Lax342547.UnaryRowLaw.pack
end Lax342547.UnaryRowLaw.pack
end

-- Lax342547.UnaryMixers
section
namespace Lax342547.UnaryMixers

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.UnaryRowLaw

abbrev Test (k n b degree K : ℕ) :=
  {x : Profile k n b degree // ∑ e, (x.val e).rank ≤ K} × Tag k × (Fin b → Binary)

noncomputable def testCountBound (k n b degree K : ℕ) : ℕ :=
  ((K + 1) ^ Fintype.card (Component (Tag k)) *
    2 ^ (Fintype.card (Coordinate k n b degree) * K + K * K)) * (2 * k + 1) * 2 ^ b

open scoped ENNReal

noncomputable def failureBound (k n b degree J K s₀ : ℕ) : ℝ≥0∞ :=
  testCountBound k n b degree K *
    (2 ^ (2 * J * K ^ 2 + (s₀ + 1) * (4 * J * (2 * k) * K)) / 2 ^ ((s₀ + 1) * n))

end Lax342547.UnaryMixers
end
