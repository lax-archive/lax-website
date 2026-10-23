-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

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

end Lax825748.LieRank
end
