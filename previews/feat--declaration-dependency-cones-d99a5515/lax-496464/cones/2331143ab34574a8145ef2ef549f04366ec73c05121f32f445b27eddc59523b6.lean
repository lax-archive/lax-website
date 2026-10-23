-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Interval.Finset.Nat

-- Lax496464.FlowShop
section
namespace Lax496464.FlowShop.Instance.JITSchedule
end Lax496464.FlowShop.Instance.JITSchedule

namespace Lax496464.FlowShop

/-- An instance of the two-stage flexible flow shop: `jobs` jobs, `machines` identical
second-stage machines, and for each job a preprocessing time, a processing time, a due
date and a weight. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of identical second-stage machines. -/
  machines : ℕ
  /-- The first-stage (preprocessing) time `p j` of job `j`. -/
  p : Fin jobs → ℕ
  /-- The second-stage (processing) time `q j` of job `j`. -/
  q : Fin jobs → ℕ
  /-- The due date `d j` of job `j`. -/
  d : Fin jobs → ℕ
  /-- The weight `w j` of job `j`. -/
  w : Fin jobs → ℕ

namespace Instance

variable (I : Instance)

variable {I}

variable (I)

end Instance

end Lax496464.FlowShop
end

-- Lax496464.Conditions
section
namespace Lax496464.Conditions
end Lax496464.Conditions
end

-- Lax496464.EstOrder
section
namespace Lax496464.EstOrder
end Lax496464.EstOrder

namespace Lax496464.EstOrder.DistinctEndpoints
end Lax496464.EstOrder.DistinctEndpoints
end

-- Lax496464.Sweep
section
namespace Lax496464.Sweep
end Lax496464.Sweep
end

-- Lax496464.Profile
section
namespace Lax496464.Profile.Printed
end Lax496464.Profile.Printed

namespace Lax496464.Profile

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Sweep

variable (I : Instance)

variable {I}

/-- The paper's `x⃗^{(q)}`: the vector `x` with coordinate `c` decremented. -/
def decAt {qmax : ℕ} (x : Fin qmax → ℕ) (c : Fin qmax) : Fin qmax → ℕ :=
  Function.update x c (x c - 1)

variable (I)

end Lax496464.Profile
end
