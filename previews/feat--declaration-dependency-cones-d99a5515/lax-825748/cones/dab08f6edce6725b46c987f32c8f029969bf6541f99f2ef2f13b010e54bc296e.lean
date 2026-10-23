-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPowerSeries.Derivative

-- Lax825748.Series
section
noncomputable section

namespace Lax825748.Series

abbrev Word (X : Type) := FreeMonoid X

abbrev NCSeries (X : Type) := Word X → ℝ

abbrev NCPolynomial (X : Type) := MonoidAlgebra ℝ (Word X)

noncomputable def pairing {X : Type} (S : NCSeries X) (P : NCPolynomial X) : ℝ :=
  P.coeff.sum fun w a => a * S w

noncomputable def wordPolynomial {X : Type} (w : Word X) : NCPolynomial X :=
  MonoidAlgebra.single w 1

noncomputable def letter {X : Type} (x : X) : NCPolynomial X :=
  wordPolynomial (FreeMonoid.of x)

noncomputable def leftResidual {X : Type} (P : NCPolynomial X)
    (S : NCSeries X) : NCSeries X :=
  fun w => pairing S (wordPolynomial w * P)

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

abbrev VectorField (d : ℕ) := Fin d → StateSeries d

noncomputable def applyVectorField {d : ℕ} (A : VectorField d)
    (f : StateSeries d) : StateSeries d :=
  ∑ i, A i * MvPowerSeries.pderiv ℝ i f

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

-- Lax825748.LieRank
section
noncomputable section

namespace Lax825748.LieRank

open Series

instance polynomialLieRing {X : Type} : LieRing (NCPolynomial X) :=
  LieRing.ofAssociativeRing

def liePolynomials (X : Type) : LieSubalgebra ℝ (NCPolynomial X) :=
  LieSubalgebra.lieSpan ℝ (NCPolynomial X) (Set.range letter)

abbrev LiePolynomial (X : Type) := liePolynomials X

noncomputable def residualSpace {X : Type} (g : NCSeries X) :
    Submodule ℝ (NCSeries X) :=
  Submodule.span ℝ {S | ∃ P : LiePolynomial X, S = leftResidual P.val g}

def HasLieRank {X : Type} (g : NCSeries X) (d : ℕ) : Prop :=
  Module.Finite ℝ (residualSpace g) ∧ Module.finrank ℝ (residualSpace g) = d

end Lax825748.LieRank
end

-- Lax825748.PBW
section
namespace Lax825748.PBW
end Lax825748.PBW
end

-- Lax825748.Shuffle
section
namespace Lax825748.Shuffle
end Lax825748.Shuffle

namespace Lax825748.Shuffle.shuffleList
end Lax825748.Shuffle.shuffleList

namespace Lax825748.Shuffle.unshuffles
end Lax825748.Shuffle.unshuffles
end

-- Lax825748.ShuffleIdentities
section
namespace Lax825748.ShuffleIdentities
end Lax825748.ShuffleIdentities

namespace Lax825748.ShuffleIdentities.distributions
end Lax825748.ShuffleIdentities.distributions
end

-- Lax825748.Annihilator
section
namespace Lax825748.Annihilator
end Lax825748.Annihilator
end

-- Lax825748.DifferentialRepresentation
section
noncomputable section

namespace Lax825748.DifferentialRepresentation

open Series FormalSeries

structure Representation (X : Type) (d : ℕ) where
  fields : X → VectorField d
  output : StateSeries d

noncomputable def act {X : Type} {d : ℕ} (R : Representation X d)
    (f : StateSeries d) (w : Word X) : StateSeries d :=
  w.toList.foldl (fun k x => applyVectorField (R.fields x) k) f

noncomputable def generatingSeries {X : Type} {d : ℕ}
    (R : Representation X d) : NCSeries X :=
  fun w => MvPowerSeries.constantCoeff (act R R.output w)

def Represents {X : Type} {d : ℕ} (R : Representation X d)
    (g : NCSeries X) : Prop := generatingSeries R = g

end Lax825748.DifferentialRepresentation
end

-- Lax825748.FormalRealization
section
namespace Lax825748.FormalRealization
end Lax825748.FormalRealization
end

-- Lax825748.FormalMinimality
section
namespace Lax825748.FormalMinimality
end Lax825748.FormalMinimality
end

-- Lax825748.Projection
section
namespace Lax825748.Projection
end Lax825748.Projection
end

-- Lax825748.RepresentationMap
section
namespace Lax825748.RepresentationMap
end Lax825748.RepresentationMap
end

-- Lax825748.FormalUniqueness
section
noncomputable section

namespace Lax825748.FormalUniqueness

open Series LieRank DifferentialRepresentation CoordinateChange

axiom minimal_realizations_equivalent {X : Type} [Finite X] {d : ℕ}
    (g : NCSeries X) (hr : HasLieRank g d)
    (R R' : Representation X d) (hR : Represents R g) (hR' : Represents R' g) :
  ∃ φ : FormalChange d,
    φ.toAlgEquiv R.output = R'.output ∧
      ∀ (k : FormalSeries.StateSeries d) (w : Word X),
        φ.toAlgEquiv (act R k w) = act R' (φ.toAlgEquiv k) w

end Lax825748.FormalUniqueness
end
