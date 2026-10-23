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
import Mathlib.LinearAlgebra.Span.Defs
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

noncomputable def rightResidual {X : Type} (S : NCSeries X)
    (P : NCPolynomial X) : NCSeries X :=
  fun w => pairing S (P * wordPolynomial w)

noncomputable def leftResidual {X : Type} (P : NCPolynomial X)
    (S : NCSeries X) : NCSeries X :=
  fun w => pairing S (wordPolynomial w * P)

noncomputable def constantSeries {X : Type} (a : ℝ) : NCSeries X := by
  classical
  exact fun w => if w = 1 then a else 0

end Lax825748.Series
end

-- Lax825748.Monomials
section
namespace Lax825748.Monomials
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
noncomputable section

namespace Lax825748.Shuffle

open Series

def unshuffles {X : Type} : List X → List (List X × List X)
  | [] => [([], [])]
  | x :: w => (unshuffles w).flatMap fun p =>
      [(x :: p.1, p.2), (p.1, x :: p.2)]

noncomputable def shuffle {X : Type} (S T : NCSeries X) : NCSeries X :=
  fun w => ((unshuffles w.toList).map fun p =>
    S (FreeMonoid.ofList p.1) * T (FreeMonoid.ofList p.2)).sum

noncomputable def shuffleList {X : Type} : List (NCSeries X) → NCSeries X
  | [] => constantSeries 1
  | S :: l => shuffle S (shuffleList l)

noncomputable def shufflePow {X : Type} (S : NCSeries X) (n : ℕ) : NCSeries X :=
  shuffleList (List.replicate n S)

end Lax825748.Shuffle
end

-- Lax825748.ShuffleIdentities
section
namespace Lax825748.ShuffleIdentities.distributions
end Lax825748.ShuffleIdentities.distributions

noncomputable section

namespace Lax825748.ShuffleIdentities

open Series Shuffle LieRank Monomials

open scoped BigOperators

noncomputable def shuffleMonomial {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (I : Fin d → ℕ) : NCSeries X :=
  shuffleList (List.ofFn fun i => shufflePow (S i) (I i))

end Lax825748.ShuffleIdentities
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

-- Lax825748.RepresentationMap
section
noncomputable section

namespace Lax825748.RepresentationMap

open Series FormalSeries DifferentialRepresentation Shuffle

noncomputable def eta {X : Type} {d : ℕ} (R : Representation X d)
    (k : StateSeries d) : NCSeries X :=
  fun w => MvPowerSeries.constantCoeff (act R k w)

end Lax825748.RepresentationMap
end

-- Lax825748.ShuffleFinite
section
noncomputable section

namespace Lax825748.ShuffleFinite

open Series Shuffle ShuffleIdentities

structure ShuffleSubalgebra (X : Type) where
  toSubmodule : Submodule ℝ (NCSeries X)
  one_mem : constantSeries 1 ∈ toSubmodule
  shuffle_mem : ∀ S T, S ∈ toSubmodule → T ∈ toSubmodule → shuffle S T ∈ toSubmodule

def FinitelyGenerated {X : Type} (A : ShuffleSubalgebra X) : Prop :=
  ∃ (n : ℕ) (S : Fin n → NCSeries X),
    A.toSubmodule = Submodule.span ℝ (Set.range fun I : Fin n → ℕ => shuffleMonomial S I)

def DerivativeStable {X : Type} (A : ShuffleSubalgebra X) : Prop :=
  ∀ (x : X) (T : NCSeries X), T ∈ A.toSubmodule →
    rightResidual T (letter x) ∈ A.toSubmodule

def IsShuffleFinite {X : Type} (f : NCSeries X) : Prop :=
  ∃ A : ShuffleSubalgebra X, FinitelyGenerated A ∧ DerivativeStable A ∧ f ∈ A.toSubmodule

end Lax825748.ShuffleFinite
end

-- Lax825748.ShuffleFiniteCoordinates
section
noncomputable section

namespace Lax825748.ShuffleFiniteCoordinates

open Series ShuffleFinite LieRank Annihilator FormalSeries

open DifferentialRepresentation RepresentationMap

axiom minimal_realization {X : Type} [Finite X] (f : NCSeries X) (k : ℕ)
    (hr : HasLieRank f k) (A : ShuffleSubalgebra X)
    (hfg : FinitelyGenerated A) (hstable : DerivativeStable A) (hf : f ∈ A.toSubmodule) :
    ∃ R : Representation X k, Represents R f ∧
      ∀ i : Fin k, eta R (MvPowerSeries.X i) ∈ A.toSubmodule ∧
        IsShuffleFinite (eta R (MvPowerSeries.X i))

end Lax825748.ShuffleFiniteCoordinates
end
