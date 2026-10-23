-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

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

/-- A job of the instance. -/
abbrev Job : Type := Fin I.jobs

variable {I}

/-- `s j = d j - q j`: the time at which job `j`'s second operation must start if `j` is
to be completed just in time, and hence a deadline for its first operation. -/
def s (j : I.Job) : ℤ := (I.d j : ℤ) - I.q j

variable (I)

end Instance

end Lax496464.FlowShop
end

-- Lax496464.EstOrder
section
namespace Lax496464.EstOrder
end Lax496464.EstOrder

namespace Lax496464.EstOrder.DistinctEndpoints
end Lax496464.EstOrder.DistinctEndpoints
end

-- Lax496464.DynamicProgram
section
namespace Lax496464.DynamicProgram.X1
end Lax496464.DynamicProgram.X1

namespace Lax496464.DynamicProgram

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- `Z` **can be preprocessed from `P`**: starting at the instant `P`, the first-stage
machine finishes each job of `Z` by the time its second operation must start. -/
def PreprocessableFrom (Z : Finset I.Job) (P : ℤ) : Prop :=
  ∀ j ∈ Z, P + ∑ i ∈ Z.filter (fun i => i ≤ j), (I.p i : ℤ) ≤ s j

end Lax496464.DynamicProgram
end
