-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Basic

-- Lax619925.IdealMembership
section
namespace Lax619925.IdealMembership

/-- Ideal membership in the multivariate polynomial ring over `ℚ` is decidable:
    given a finite set of generators, there is a decision procedure `dec` such
    that `dec p = true` iff `p` lies in the ideal the generators span.  Proven
    in the proofs package by a classical argument (excluded middle supplies the
    characteristic function); the constructive Gröbner-basis procedure is out
    of scope. -/
axiom IdealMembershipDecidable (k : ℕ) (gens : Finset (MvPolynomial (Fin k) ℚ)) :
  ∃ dec : MvPolynomial (Fin k) ℚ → Bool, ∀ p, dec p = true ↔ p ∈ Ideal.span ↑gens

end Lax619925.IdealMembership
end
