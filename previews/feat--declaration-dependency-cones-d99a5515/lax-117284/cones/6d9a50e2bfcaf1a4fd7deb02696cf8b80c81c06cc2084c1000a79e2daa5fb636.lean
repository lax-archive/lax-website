-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Order.Interval.Set.Basic

-- Lax117284.Scheduling
section
namespace Lax117284
end Lax117284

namespace Lax117284.Scheduling
end Lax117284.Scheduling

namespace Lax117284.Scheduling.Instance
end Lax117284.Scheduling.Instance
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
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

-- Lax117284.Problems
section
namespace Lax117284.Problems
end Lax117284.Problems
end

-- Lax117284.JustInTime
section
namespace Lax117284.JustInTime

open Lax434930.PolynomialTime

/-- An instance of `R || ∑_j Z_j`: `jobs` jobs and `machines` unrelated machines, where job
`j` has due date `d j` and processing time `p i j` on machine `i`. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of machines. -/
  machines : ℕ
  /-- The processing time `p i j` of job `j` on machine `i`. -/
  p : Fin machines → Fin jobs → ℕ
  /-- The due date `d j` of job `j`, the same on every machine. -/
  d : Fin jobs → ℕ
  /-- Every job takes some time. -/
  p_pos : ∀ i j, 0 < p i j
  /-- No job starts before time `0`. -/
  p_le_d : ∀ i j, p i j ≤ d j

namespace Instance

variable (R : Instance)

/-- The interval `(d j - p i j, d j]` occupied by job `j` when it is executed just in time
on machine `i`. -/
def job (i : Fin R.machines) (j : Fin R.jobs) : Set ℕ :=
  Set.Ioc (R.d j - R.p i j) (R.d j)

end Instance

end Lax117284.JustInTime
end
