-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

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

-- Lax496464.BinaryEncoding
section
namespace Lax496464.BinaryEncoding

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax434930.PolynomialTime

/-- The largest number appearing in an instance. A reduction witnesses *strong*
NP-hardness when this stays polynomial in the length of its input. -/
def maxNumber (I : Instance) : ℕ :=
  ((List.finRange I.jobs).map fun j =>
      max (max (I.p j) (I.q j)) (max (I.d j) (I.w j))).foldr max (max I.jobs I.machines)

end Lax496464.BinaryEncoding
end
