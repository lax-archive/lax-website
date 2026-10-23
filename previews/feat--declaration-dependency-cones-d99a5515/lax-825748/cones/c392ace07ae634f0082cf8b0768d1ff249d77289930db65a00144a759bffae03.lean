-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPowerSeries.Derivative

-- Lax825748.Series
section
namespace Lax825748
end Lax825748

namespace Lax825748.Series
end Lax825748.Series
end

-- Lax825748.Monomials
section
noncomputable section

namespace Lax825748.Monomials

open Series

open scoped BigOperators

def totalDegree {d : ℕ} (I : Fin d → ℕ) : ℕ := ∑ j, I j

end Lax825748.Monomials
end

-- Lax825748.FormalSeries
section
noncomputable section

namespace Lax825748.FormalSeries

open Monomials

open scoped BigOperators

abbrev StateSeries (d : ℕ) := MvPowerSeries (Fin d) ℝ

def AgreeBelow {d : ℕ} (N : ℕ) (f g : StateSeries d) : Prop :=
  ∀ I : Fin d →₀ ℕ, totalDegree I < N →
    MvPowerSeries.coeff I f = MvPowerSeries.coeff I g

def FormallyContinuous {d e : ℕ} (F : StateSeries d → StateSeries e) : Prop :=
  ∀ N, ∃ M, ∀ f g, AgreeBelow M f g → AgreeBelow N (F f) (F g)

end Lax825748.FormalSeries
end

-- Lax825748.ConvergentSeries
section
noncomputable section

namespace Lax825748.ConvergentSeries

open Lax825748.FormalSeries Lax825748.Monomials

def HasGeometricBound {d : ℕ} (f : StateSeries d) (α C : ℝ) : Prop :=
  ∀ I : Fin d →₀ ℕ, |MvPowerSeries.coeff I f| ≤ α * C ^ totalDegree I

def Convergent {d : ℕ} (f : StateSeries d) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧ HasGeometricBound f α C

end Lax825748.ConvergentSeries
end

-- Lax825748.CoordinateChange
section
noncomputable section

namespace Lax825748.CoordinateChange

open FormalSeries

structure FormalChange (d : ℕ) where
  toAlgEquiv : StateSeries d ≃ₐ[ℝ] StateSeries d
  continuous_toFun : FormallyContinuous toAlgEquiv
  continuous_invFun : FormallyContinuous toAlgEquiv.symm
  origin : ∀ i, MvPowerSeries.constantCoeff (toAlgEquiv (MvPowerSeries.X i)) = 0
  inverse_origin : ∀ i,
    MvPowerSeries.constantCoeff (toAlgEquiv.symm (MvPowerSeries.X i)) = 0

end Lax825748.CoordinateChange
end

-- Lax825748.AnalyticChanges
section
noncomputable section

namespace Lax825748.AnalyticChanges

open Lax825748.FormalSeries Lax825748.CoordinateChange ConvergentSeries

structure AnalyticChange (d : ℕ) extends FormalChange d where
  convergent_toFun : ∀ i, Convergent (toAlgEquiv (MvPowerSeries.X i))
  convergent_invFun : ∀ i, Convergent (toAlgEquiv.symm (MvPowerSeries.X i))

end Lax825748.AnalyticChanges
end
