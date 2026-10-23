-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

-- Lax109476.LinearProgram
section
open scoped BigOperators

namespace Lax109476.LinearProgram

/-- Coefficients of a maximization program with `m` inequalities and `n`
nonnegative variables. -/
structure Program (K : Type) (m n : ℕ) where
  /-- The constraint matrix. -/
  A : Fin m → Fin n → K
  /-- The upper bounds on the constraint rows. -/
  b : Fin m → K
  /-- The coefficients of the maximized objective. -/
  c : Fin n → K

end Lax109476.LinearProgram
end

-- Lax109476.FarkasCertificate
section
namespace Lax109476.FarkasCertificate
end Lax109476.FarkasCertificate
end

-- Lax109476.RecessionDirection
section
namespace Lax109476.RecessionDirection
end Lax109476.RecessionDirection
end

-- Lax109476.RationalCertificates
section
namespace Lax109476.RationalCertificates.Certificate
end Lax109476.RationalCertificates.Certificate

namespace Lax109476.RationalCertificates.IsValidCertificate
end Lax109476.RationalCertificates.IsValidCertificate

namespace Lax109476.RationalCertificates.Certificate.infeasible
end Lax109476.RationalCertificates.Certificate.infeasible

namespace Lax109476.RationalCertificates.Certificate.optimal
end Lax109476.RationalCertificates.Certificate.optimal

namespace Lax109476.RationalCertificates.Certificate.unbounded
end Lax109476.RationalCertificates.Certificate.unbounded

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

/-- Interpret rational coefficient data as a real linear program. -/
def toReal {m n : ℕ} (P : Program ℚ m n) : Program ℝ m n where
  A i j := P.A i j
  b i := P.b i
  c j := P.c j

end Lax109476.RationalCertificates
end
