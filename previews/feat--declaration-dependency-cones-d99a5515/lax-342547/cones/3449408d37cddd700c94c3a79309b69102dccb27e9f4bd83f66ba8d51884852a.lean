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

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.LowRankCounting
section
namespace Lax342547.LowRankCounting
end Lax342547.LowRankCounting
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

-- Lax342547.HoleRelation
section
namespace Lax342547
end Lax342547

namespace Lax342547.HoleRelation
end Lax342547.HoleRelation

namespace Lax342547.HoleRelation.HoleData
end Lax342547.HoleRelation.HoleData
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

-- Lax342547.FormalQuadratic
section
namespace Lax342547.FormalQuadratic

variable {K B : Type} [Field K] [Fintype B] {V : B → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

abbrev Rows (V : B → Type) := ∀ i, V i × V i

open Lax342547.MomentSpace

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

open Lax342547.MomentSpace

variable {E I : Type} [Fintype E] [Fintype I]

abbrev Block (inc : Finset E) (J : ℕ) :=
  (Fin J × E × {f : E // f ∈ inc}) ⊕ (Fin J × {e : E // e ∈ inc} × E)

def blockRank (r : E → ℕ) {inc : Finset E} {J : ℕ} : Block inc J → ℕ
  | .inl (_, e, _) => r e
  | .inr (_, _, f) => r f

abbrev Rows (r : E → ℕ) (inc : Finset E) (J : ℕ) :=
  FormalQuadratic.Rows (fun t : Block inc J => Fin (blockRank r t) → Binary)

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut

open Lax342547.CutProfiles Lax342547.Atoms

end Lax342547.UnaryMixer
end

-- Lax342547.UnaryRowLaw
section
namespace Lax342547.UnaryRowLaw.pack
end Lax342547.UnaryRowLaw.pack

namespace Lax342547.UnaryRowLaw

open Lax342547.MomentSpace Lax342547.UnaryMixer

variable {E I N : Type} [Fintype E] [Fintype I] [Fintype N]

abbrev RowIndex (r : E → ℕ) (inc : Finset E) (J : ℕ) :=
  (t : Block inc J) × (Fin (blockRank r t) ⊕ Fin (blockRank r t))

def flatten {r : E → ℕ} {inc : Finset E} {J : ℕ} :
    Rows r inc J ≃ₗ[Binary] (RowIndex r inc J → Binary) where
  toFun x a := Sum.elim (x a.1).1 (x a.1).2 a.2
  invFun y t := (fun a => y ⟨t, .inl a⟩, fun a => y ⟨t, .inr a⟩)
  left_inv x := rfl
  right_inv y := by funext a; rcases a with ⟨t, a | a⟩ <;> rfl
  map_add' x y := by funext a; rcases a with ⟨t, a | a⟩ <;> rfl
  map_smul' a x := by funext b; rcases b with ⟨t, b | b⟩ <;> rfl

open scoped ENNReal

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut Lax342547.CutProfiles

end Lax342547.UnaryRowLaw
end
