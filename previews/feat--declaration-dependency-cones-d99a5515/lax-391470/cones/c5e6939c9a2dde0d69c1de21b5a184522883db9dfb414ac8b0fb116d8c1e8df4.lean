-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

-- Lax391470.StackedConstruction
section
namespace Lax391470.StackedConstruction.inst
end Lax391470.StackedConstruction.inst

namespace Lax391470.StackedConstruction

open Lax391470.Scheduling Lax391470.AuxiliaryProblem

variable (p q : ℕ) (A : AuxiliaryProblem.Instance)

/-- Which of the five jobs of its pair a job is: `0` the separator, `1` the inner long
job, `2` the outer long job, `3` the inner short job, `4` the outer short job. -/
def partOf (j : ℕ) : ℕ := (j - A.ordinary) % 5

end Lax391470.StackedConstruction
end
