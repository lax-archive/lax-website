-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Real.Basic

-- Lax391470.Scheduling
section
namespace Lax391470.Scheduling

/-- An instance of single machine scheduling with release times and deadlines: `jobs`
jobs, each with a release time, a deadline and a processing time. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The release time `r i` of job `i`. -/
  r : Fin jobs → ℤ
  /-- The deadline `d i` of job `i`. -/
  d : Fin jobs → ℤ
  /-- The processing time `p i` of job `i`. -/
  p : Fin jobs → ℕ

namespace Instance

variable (I : Instance)

variable {I}

variable (I)

end Instance

end Lax391470.Scheduling
end

-- Lax391470.AuxiliaryProblem
section
namespace Lax391470.AuxiliaryProblem
end Lax391470.AuxiliaryProblem

namespace Lax391470.AuxiliaryProblem.Instance
end Lax391470.AuxiliaryProblem.Instance

namespace Lax391470.AuxiliaryProblem.Instance.Ordered
end Lax391470.AuxiliaryProblem.Instance.Ordered
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax391470.BinaryEncoding
section
namespace Lax391470.BinaryEncoding
end Lax391470.BinaryEncoding
end

-- Lax391470.StackedConstruction
section
namespace Lax391470.StackedConstruction
end Lax391470.StackedConstruction

namespace Lax391470.StackedConstruction.inst
end Lax391470.StackedConstruction.inst
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
end

-- Lax391470.Lemma1
section
namespace Lax391470.Lemma1

open Lax391470.BinaryEncoding Lax434930.PolynomialTime Lax429075.Reductions

/-- An instance on the lengths `{p, q}` without a feasible schedule, when `p ≥ 1`: one job
of length `p` that is due when it is released. -/
def blocked (p : ℕ) : Scheduling.Instance where
  jobs := 1
  r _ := 0
  d _ := 0
  p _ := p

end Lax391470.Lemma1
end
