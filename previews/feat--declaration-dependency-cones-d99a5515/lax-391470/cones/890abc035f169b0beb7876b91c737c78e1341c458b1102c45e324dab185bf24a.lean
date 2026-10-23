-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Real.Basic

-- Lax391470.Scheduling
section
namespace Lax391470
end Lax391470

namespace Lax391470.Scheduling
end Lax391470.Scheduling

namespace Lax391470.Scheduling.Instance
end Lax391470.Scheduling.Instance
end

-- Lax391470.AuxiliaryProblem
section
namespace Lax391470.AuxiliaryProblem.Instance.Ordered
end Lax391470.AuxiliaryProblem.Instance.Ordered

namespace Lax391470.AuxiliaryProblem

open Lax391470.Scheduling

/-- The data of an instance of `AUX(p, q)`: ordinary jobs, each long or short, and
`pairs` connected pairs of pending jobs with an early and a late deadline each. -/
structure Instance where
  /-- The number of ordinary jobs. -/
  ordinary : ℕ
  /-- The release time of an ordinary job. -/
  r : Fin ordinary → ℕ
  /-- The deadline of an ordinary job. -/
  d : Fin ordinary → ℕ
  /-- Whether an ordinary job is long (of length `p`) rather than short (of length `q`). -/
  long : Fin ordinary → Bool
  /-- The number `N` of connected pairs of pending jobs. -/
  pairs : ℕ
  /-- The early deadline `d'_{p,i}` of the `i`-th long pending job. -/
  longEarly : Fin pairs → ℕ
  /-- The late deadline `d_{p,i}` of the `i`-th long pending job. -/
  longDue : Fin pairs → ℕ
  /-- The early deadline `d'_{q,i}` of the `i`-th short pending job. -/
  shortEarly : Fin pairs → ℕ
  /-- The late deadline `d_{q,i}` of the `i`-th short pending job. -/
  shortDue : Fin pairs → ℕ

namespace Instance

variable (A : Instance)

variable {A}

variable (A)

end Instance

end Lax391470.AuxiliaryProblem
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

-- Lax429075.CNF
section
namespace Lax429075
end Lax429075

namespace Lax429075.CNF
end Lax429075.CNF

namespace Lax429075.CNF.Literal
end Lax429075.CNF.Literal
end

-- Lax391470.SatConstruction
section
namespace Lax391470.SatConstruction
end Lax391470.SatConstruction

namespace Lax391470.SatConstruction.ordRelease
end Lax391470.SatConstruction.ordRelease
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

-- Lax429075.Encoding
section
namespace Lax429075.Encoding
end Lax429075.Encoding

namespace Lax429075.Encoding.decodeCNF
end Lax429075.Encoding.decodeCNF

namespace Lax429075.Encoding.encodeList
end Lax429075.Encoding.encodeList

namespace Lax429075.Encoding.parseList
end Lax429075.Encoding.parseList

namespace Lax429075.Encoding.parseLiteral
end Lax429075.Encoding.parseLiteral

namespace Lax429075.Encoding.parseNat
end Lax429075.Encoding.parseNat
end

-- Lax429075.Satisfiability
section
namespace Lax429075.Satisfiability
end Lax429075.Satisfiability
end

-- Lax391470.Lemma2
section
namespace Lax391470.Lemma2.reduce
end Lax391470.Lemma2.reduce

namespace Lax391470.Lemma2

open Lax391470.BinaryEncoding Lax434930.PolynomialTime

open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

/-- An instance of the auxiliary problem without a solution, when `q ≥ 1`: one ordinary
short job, released and due at time `0`. -/
def blocked : AuxiliaryProblem.Instance where
  ordinary := 1
  r _ := 0
  d _ := 0
  long _ := false
  pairs := 0
  longEarly := Fin.elim0
  longDue := Fin.elim0
  shortEarly := Fin.elim0
  shortDue := Fin.elim0

end Lax391470.Lemma2
end
