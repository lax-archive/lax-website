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
namespace Lax496464.Profile

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Sweep

variable (I : Instance)

/-- The **due-date profile** of `Z` at `t`: the number of jobs of `Z` due at `t + i`. -/
def dueProfile (Z : Finset I.Job) (t : ℤ) (i : ℕ) : ℕ :=
  (Z.filter fun k => (I.d k : ℤ) = t + i).card

/-- The start time of the job before `k`, and `0` before the first job. -/
def sBefore (k : I.Job) : ℤ :=
  if h : (k : ℕ) = 0 then 0 else s (⟨(k : ℕ) - 1, by omega⟩ : I.Job)

/-- The paper's `δⱼ`: how far the reference point moves at job `k`. -/
def delta (k : I.Job) : ℕ := (s k - sBefore I k).toNat

variable {I}

/-- The paper's `x⃗^{(q)}`: the vector `x` with coordinate `c` decremented. -/
def decAt {qmax : ℕ} (x : Fin qmax → ℕ) (c : Fin qmax) : Fin qmax → ℕ :=
  Function.update x c (x c - 1)

variable (I)

/-- **Recursion (5), exactly as printed.** The entries it derives: the base
`T₀[0⃗, 0] = 0`, the convention `Tⱼ[0⃗, 0] = 0`, the capacity test `∑ xᵢ ≤ m` and `W' > 0`
on every other entry, and the two branches, each through the printed shift — which
constrains the earlier vector only on the coordinates at or above `δ`. -/
inductive Printed (qmax : ℕ) : ℕ → (Fin qmax → ℕ) → ℕ → ℤ → Prop
  /-- Before the first job, the empty selection. -/
  | init : Printed qmax 0 0 0 0
  /-- At any stage, the empty selection. -/
  | zero (t : ℕ) : Printed qmax t 0 0 0
  /-- Job `k` is passed over. -/
  | skip {k : I.Job} {x y : Fin qmax → ℕ} {W : ℕ} {P : ℤ}
      (hcap : ∑ i, x i ≤ I.machines) (hW : 0 < W)
      (hshift : ∀ i : Fin qmax, ∀ hi : delta I k ≤ (i : ℕ),
        y i = x ⟨(i : ℕ) - delta I k, by have := i.isLt; omega⟩)
      (h : Printed qmax (k : ℕ) y W P) : Printed qmax ((k : ℕ) + 1) x W P
  /-- Job `k` is selected. -/
  | take {k : I.Job} {x y : Fin qmax → ℕ} {W : ℕ} {P : ℤ} (c : Fin qmax)
      (hc : (c : ℕ) + 1 = I.q k) (hxc : 1 ≤ x c)
      (hcap : ∑ i, x i ≤ I.machines) (hW : 0 < W) (hwW : I.w k ≤ W)
      (hshift : ∀ i : Fin qmax, ∀ hi : delta I k ≤ (i : ℕ),
        y i = decAt x c ⟨(i : ℕ) - delta I k, by have := i.isLt; omega⟩)
      (h : Printed qmax (k : ℕ) y (W - I.w k) P) (hfit : P + I.p k ≤ s k) :
      Printed qmax ((k : ℕ) + 1) x W (P + I.p k)

end Lax496464.Profile
end

-- Lax496464.Lemma3
section
namespace Lax496464.Lemma3

open Lax496464.FlowShop Lax496464.FlowShop.Instance

open Lax496464.Sweep Lax496464.Profile

variable (I : Instance)

/-- **Lemma 3 is false as printed.** Some instance, with positive processing times and
positive weights, has a stage at which the printed recursion derives a profile that no
set of jobs has. -/
axiom printed_not_correct :
    ∃ (J : Instance) (qmax : ℕ) (k : J.Job) (x : Fin qmax → ℕ) (W : ℕ) (P : ℤ),
      (∀ i : J.Job, 0 < J.q i) ∧ (∀ i : J.Job, 0 < J.w i) ∧
      (∀ i : J.Job, J.q i ≤ qmax) ∧
      Printed J qmax ((k : ℕ) + 1) x W P ∧
      ∀ Z : Finset J.Job, ∃ c : Fin qmax,
        dueProfile J Z (s k) ((c : ℕ) + 1) ≠ x c

end Lax496464.Lemma3
end
