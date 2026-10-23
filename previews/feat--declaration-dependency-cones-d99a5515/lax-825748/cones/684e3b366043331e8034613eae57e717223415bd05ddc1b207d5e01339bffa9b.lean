-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

-- Lax825748.Series
section
noncomputable section

namespace Lax825748.Series

abbrev Word (X : Type) := FreeMonoid X

abbrev NCPolynomial (X : Type) := MonoidAlgebra ℝ (Word X)

noncomputable def wordPolynomial {X : Type} (w : Word X) : NCPolynomial X :=
  MonoidAlgebra.single w 1

noncomputable def letter {X : Type} (x : X) : NCPolynomial X :=
  wordPolynomial (FreeMonoid.of x)

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

end Lax825748.LieRank
end

-- Lax825748.PBW
section
noncomputable section

namespace Lax825748.PBW

open Series LieRank

abbrev OrderedWord (ι : Type) [LinearOrder ι] :=
  {l : List ι // l.Pairwise (· ≤ ·)}

noncomputable def monomial {X ι : Type} [LinearOrder ι]
    (b : Module.Basis ι ℝ (LiePolynomial X)) (l : OrderedWord ι) : NCPolynomial X :=
  (l.val.map fun i => (b i).val).prod

end Lax825748.PBW
end
