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
noncomputable section

namespace Lax825748.Series

abbrev Word (X : Type) := FreeMonoid X

abbrev NCSeries (X : Type) := Word X → ℝ

abbrev NCPolynomial (X : Type) := MonoidAlgebra ℝ (Word X)

noncomputable def pairing {X : Type} (S : NCSeries X) (P : NCPolynomial X) : ℝ :=
  P.coeff.sum fun w a => a * S w

noncomputable def wordPolynomial {X : Type} (w : Word X) : NCPolynomial X :=
  MonoidAlgebra.single w 1

noncomputable def rightResidual {X : Type} (S : NCSeries X)
    (P : NCPolynomial X) : NCSeries X :=
  fun w => pairing S (P * wordPolynomial w)

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

end Lax825748.DifferentialRepresentation
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

-- Lax825748.RepresentationMap
section
noncomputable section

namespace Lax825748.RepresentationMap

open Series FormalSeries DifferentialRepresentation Shuffle

noncomputable def eta {X : Type} {d : ℕ} (R : Representation X d)
    (k : StateSeries d) : NCSeries X :=
  fun w => MvPowerSeries.constantCoeff (act R k w)

axiom intertwining {X : Type} {d : ℕ} (R : Representation X d)
    (k : StateSeries d) (w : Word X) :
  eta R (act R k w) = rightResidual (eta R k) (wordPolynomial w)

end Lax825748.RepresentationMap
end
