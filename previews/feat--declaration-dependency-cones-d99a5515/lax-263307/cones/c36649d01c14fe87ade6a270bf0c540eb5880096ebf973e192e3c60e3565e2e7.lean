-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

-- Lax109476.LinearProgram
section
namespace Lax109476
end Lax109476

namespace Lax109476.LinearProgram
end Lax109476.LinearProgram

namespace Lax109476.LinearProgram.Program
end Lax109476.LinearProgram.Program
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
namespace Lax109476.RationalCertificates
end Lax109476.RationalCertificates

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
end

-- Lax109476.CertificateSoundness
section
namespace Lax109476.CertificateSoundness
end Lax109476.CertificateSoundness
end

-- Lax263307.DistanceProjection
section
namespace Lax263307
end Lax263307

namespace Lax263307.DistanceProjection
end Lax263307.DistanceProjection
end

-- Lax263307.RationalProjection
section
namespace Lax263307.RationalProjection.Correct
end Lax263307.RationalProjection.Correct

namespace Lax263307.RationalProjection.classify
end Lax263307.RationalProjection.classify

namespace Lax263307.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates

open DistanceProjection

inductive Outcome (n : ℕ)
  | near (point : Fin n → ℚ)
  | far (normal : Fin n → ℚ) (bound : ℚ)
  | reject

end Lax263307.RationalProjection
end
