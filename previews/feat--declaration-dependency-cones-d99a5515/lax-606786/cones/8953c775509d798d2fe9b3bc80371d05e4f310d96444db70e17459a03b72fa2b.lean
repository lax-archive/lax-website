-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.Closeds

-- Lax606786.ExtendedLog
section
namespace Lax606786
end Lax606786

namespace Lax606786.ExtendedLog
end Lax606786.ExtendedLog
end

-- Lax606786.BanachGrassmannian
section
namespace Lax606786.BanachGrassmannian

open TopologicalSpace

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {X}

namespace Grassmannian

end Grassmannian

variable (X)

/-- `𝒢_k X`: the `k`-dimensional subspaces of `X`. -/
def GrassmannianFin (k : ℕ) : Type _ :=
  {V : Submodule ℝ X // FiniteDimensional ℝ V ∧ Module.finrank ℝ V = k}

variable {X}

namespace GrassmannianFin

end GrassmannianFin

end Lax606786.BanachGrassmannian
end

-- Lax606786.OperatorStatistics
section
namespace Lax606786.OperatorStatistics
end Lax606786.OperatorStatistics
end

-- Lax606786.TemperedFunctions
section
namespace Lax606786
end Lax606786

namespace Lax606786.TemperedFunctions
end Lax606786.TemperedFunctions
end

-- Lax606786.Cocycles
section
namespace Lax606786.Cocycles.Cocycle.iterate
end Lax606786.Cocycles.Cocycle.iterate

namespace Lax606786.Cocycles.Cocycle.lambdaIdx
end Lax606786.Cocycles.Cocycle.lambdaIdx

namespace Lax606786.Cocycles

open MeasureTheory Filter

open Lax606786.OperatorStatistics Lax606786.ExtendedLog Lax606786.TemperedFunctions

variable {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]

/-- A strongly measurable, forward-integrable cocycle of bounded operators on `X` over an
invertible ergodic transformation of a Lebesgue probability space. -/
structure Cocycle (Ω X : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] where
  /-- The base transformation, a measurable bijection with measurable inverse. -/
  σ : Ω ≃ᵐ Ω
  /-- The invariant measure. -/
  μ : Measure Ω
  /-- The generator `ω ↦ 𝓛_ω`. -/
  L : Ω → X →L[ℝ] X
  isProbability : IsProbabilityMeasure μ
  nullSingleton : NullSingletonClass μ
  ergodic : Ergodic σ μ
  stronglyMeasurable : ∀ x : X, Measurable (fun ω => L ω x)
  forwardIntegrable : Integrable (fun ω => Real.log (max ‖L ω‖ 1)) μ

attribute [instance] Cocycle.isProbability Cocycle.nullSingleton

namespace Cocycle

end Cocycle

end Lax606786.Cocycles
end

-- Lax606786.OseledetsDecompositions
section
namespace Lax606786.OseledetsDecompositions

open MeasureTheory Filter TopologicalSpace

open Lax606786.BanachGrassmannian Lax606786.OperatorStatistics Lax606786.ExtendedLog
  Lax606786.Cocycles

/-- The sum `E_1(ω) ⊕ ⋯ ⊕ E_l(ω)` of the first `l` fast spaces (of those that exist). -/
def fastSum {Ω X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℕ∞} {m : ℕ → ℕ+}
    (E : ∀ i : ℕ, 1 ≤ i → (i : ℕ∞) < L → Ω → GrassmannianFin X (m i))
    (l : ℕ) (ω : Ω) : Submodule ℝ X :=
  ⨆ (i : ℕ) (h₁ : 1 ≤ i) (h₂ : (i : ℕ∞) < L) (_ : i ≤ l), ((E i h₁ h₂ ω).1 : Submodule ℝ X)

end Lax606786.OseledetsDecompositions
end
