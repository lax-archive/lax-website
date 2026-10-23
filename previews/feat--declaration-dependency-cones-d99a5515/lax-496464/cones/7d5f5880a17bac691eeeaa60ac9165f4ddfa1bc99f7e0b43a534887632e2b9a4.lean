-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

-- Lax496464.FlowShop
section
namespace Lax496464
end Lax496464

namespace Lax496464.FlowShop
end Lax496464.FlowShop

namespace Lax496464.FlowShop.Instance
end Lax496464.FlowShop.Instance

namespace Lax496464.FlowShop.Instance.JITSchedule
end Lax496464.FlowShop.Instance.JITSchedule
end

-- Lax496464.WordEncoding
section
namespace Lax496464.WordEncoding.EncodesInstance
end Lax496464.WordEncoding.EncodesInstance

namespace Lax496464.WordEncoding

open Lax496464.FlowShop Lax496464.FlowShop.Instance

/-- The number of jobs declared by a word: its first entry. -/
def jobCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The due date of job `j`, from the block following the processing times. -/
def due (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + 2 * jobCount x + j) 0

end Lax496464.WordEncoding
end
