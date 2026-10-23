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

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

instance (b degree : ℕ) : Fintype (SelectorCoordinates b degree) :=
  inferInstanceAs (Fintype {S : Finset (Fin b) // S.card ≤ degree})

def selectorEval {b degree : ℕ} (s : Fin b → Binary)
    (c : SelectorCoordinates b degree) : Binary := ∏ i ∈ c.val, s i

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

def shared {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (0, i)

def free {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (2, i)

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

-- Lax342547.AtomDirections
section
namespace Lax342547.AtomDirections

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

noncomputable def blockDirections {k n b degree : ℕ} (s : Fin b → Binary)
    (c : Fin n → Base k n) : Matrix (Coordinate k n b degree) (Fin n) Binary := by
  classical
  exact fun i j => if i.2 = some (c j) then selectorEval s i.1 else 0

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

variable {K I N P : Type} [Field K] [Fintype I]

def orders (D : Matrix I N K) (E : Matrix I P K) :
    Matrix I I K →ₗ[K] (Matrix N P K × Matrix P N K) where
  toFun L := (D.transpose * L * E, E.transpose * L * D)
  map_add' L M := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a L := by simp [Matrix.mul_smul, Matrix.smul_mul]

def parity (a b : K) : (Matrix N P K × Matrix P N K) →ₗ[K] Matrix N P K where
  toFun x := a • x.1 + b • x.2.transpose
  map_add' x y := by simp [smul_add, add_add_add_comm]
  map_smul' c x := by simp [smul_add, smul_smul, mul_comm]

def familyParity {F : Type} [Fintype F] (D : Matrix I N K) (E : Matrix I P K) (a b : F → K) :
    (F → Matrix I I K) →ₗ[K] Matrix N P K :=
  ∑ j, ((parity (a j) (b j)).comp (orders D E)).comp (LinearMap.proj j)

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.AtomDirections

open scoped ENNReal

end Lax342547.OrderedMixerLaw
end

-- Lax342547.SharpMixerLaw
section
namespace Lax342547.SharpMixerLaw
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

def MixerGood {k n b degree : ℕ} {F : Type} [Fintype F]
    (L : F → Moment k n b degree) : Prop :=
  ∀ s t : Fin b → Binary, s ≠ t → ∀ a b' : F → Binary,
    (∃ j, a j ≠ 0 ∨ b' j ≠ 0) →
      n ≤ 5 * (OrderedMixerLaw.familyParity (blockDirections s free)
        (blockDirections t free) a b' L).rank

open scoped ENNReal

end Lax342547.BinaryMixers
end
