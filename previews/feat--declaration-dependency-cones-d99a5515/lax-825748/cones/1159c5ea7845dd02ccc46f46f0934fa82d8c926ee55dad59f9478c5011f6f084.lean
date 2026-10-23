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
