-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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

def multiFactorial {d : ℕ} (I : Fin d → ℕ) : ℕ := ∏ j, (I j).factorial

noncomputable def orderedPowers {X : Type} {d : ℕ}
    (P : Fin d → NCPolynomial X) (I : Fin d → ℕ) : NCPolynomial X :=
  (List.ofFn fun j => P j ^ I j).prod

end Lax825748.Monomials
end

-- Lax825748.FormalSeries
section
noncomputable section

namespace Lax825748.FormalSeries

open Monomials

open scoped BigOperators

abbrev StateSeries (d : ℕ) := MvPowerSeries (Fin d) ℝ

abbrev VectorField (d : ℕ) := Fin d → StateSeries d

noncomputable def applyVectorField {d : ℕ} (A : VectorField d)
    (f : StateSeries d) : StateSeries d :=
  ∑ i, A i * MvPowerSeries.pderiv ℝ i f

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

-- Lax825748.AnalyticCalculus
section
namespace Lax825748.AnalyticCalculus
end Lax825748.AnalyticCalculus
end

-- Lax825748.CoordinateChange
section
namespace Lax825748.CoordinateChange
end Lax825748.CoordinateChange

namespace Lax825748.CoordinateChange.FormalChange
end Lax825748.CoordinateChange.FormalChange
end

-- Lax825748.AnalyticChanges
section
namespace Lax825748.AnalyticChanges
end Lax825748.AnalyticChanges

namespace Lax825748.AnalyticChanges.AnalyticChange
end Lax825748.AnalyticChanges.AnalyticChange
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

-- Lax825748.ConvergenceHypothesis
section
noncomputable section

namespace Lax825748.ConvergenceHypothesis

open Lax825748.Series Lax825748.LieRank Lax825748.Monomials

def Holds {X : Type} (g : NCSeries X) : Prop :=
  ∀ (q : ℕ) (P : Fin q → LiePolynomial X),
    ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧
      ∀ I : Fin q → ℕ,
        |pairing g (orderedPowers (fun j => (P j).val) I)| ≤
          α * C ^ totalDegree I * (multiFactorial I : ℝ)

end Lax825748.ConvergenceHypothesis
end

-- Lax825748.PBWConvergence
section
namespace Lax825748.PBWConvergence
end Lax825748.PBWConvergence
end

-- Lax825748.AnalyticCoordinates
section
namespace Lax825748.AnalyticCoordinates
end Lax825748.AnalyticCoordinates
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

-- Lax825748.AnalyticRepresentations
section
noncomputable section

namespace Lax825748.AnalyticRepresentations

open Lax825748.Series Lax825748.DifferentialRepresentation ConvergentSeries

def IsAnalytic {X : Type} {d : ℕ} (R : Representation X d) : Prop :=
  Convergent R.output ∧ ∀ x i, Convergent (R.fields x i)

end Lax825748.AnalyticRepresentations
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

-- Lax825748.FactorialEstimate
section
namespace Lax825748.FactorialEstimate
end Lax825748.FactorialEstimate
end

-- Lax825748.NecessaryConvergence
section
namespace Lax825748.NecessaryConvergence
end Lax825748.NecessaryConvergence
end

-- Lax825748.ResidualConvergence
section
namespace Lax825748.ResidualConvergence
end Lax825748.ResidualConvergence
end

-- Lax825748.Realization
section
namespace Lax825748.Realization
end Lax825748.Realization
end

-- Lax825748.Minimality
section
noncomputable section

namespace Lax825748.Minimality

open Lax825748.Series Lax825748.LieRank Lax825748.DifferentialRepresentation

open AnalyticRepresentations

def IsLeastDimension {X : Type} (g : NCSeries X) (d : ℕ) : Prop :=
  (∃ R : Representation X d, IsAnalytic R ∧ Represents R g) ∧
    ∀ e, (∃ R : Representation X e, IsAnalytic R ∧ Represents R g) → d ≤ e

axiom least_dimension {X : Type} [Finite X] (g : NCSeries X) (d : ℕ) :
  (HasLieRank g d ∧ ConvergenceHypothesis.Holds g) ↔ IsLeastDimension g d

end Lax825748.Minimality
end
