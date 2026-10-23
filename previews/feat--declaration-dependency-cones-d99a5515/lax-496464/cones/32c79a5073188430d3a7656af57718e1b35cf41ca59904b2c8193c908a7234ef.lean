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
namespace Lax496464.DynamicProgram

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- The paper's `j₁`: the smallest index above `j` that is not already a threshold. -/
noncomputable def j1 (X : Finset I.Job) (j : I.Job) : Option I.Job :=
  letI := Classical.decPred fun x : I.Job => x ∉ X ∧ j < x
  if h : (Finset.univ.filter fun x : I.Job => x ∉ X ∧ j < x).Nonempty then
    some ((Finset.univ.filter fun x : I.Job => x ∉ X ∧ j < x).min' h) else none

/-- The paper's `X₁`: the thresholds after `j` is passed over. -/
noncomputable def X1 (X : Finset I.Job) (j : I.Job) : Finset I.Job :=
  match j1 I X j with
  | some y => insert y (X.erase j)
  | none => X.erase j

end Lax496464.DynamicProgram
end
