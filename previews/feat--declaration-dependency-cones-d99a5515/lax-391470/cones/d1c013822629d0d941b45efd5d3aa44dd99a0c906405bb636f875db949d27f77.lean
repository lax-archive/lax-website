-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

/-- The conditions on the deadlines of the pending jobs: within each sequence the
intervals between early and late deadline are ordered and do not intersect, and in every
connected pair the long job is the more urgent. -/
structure Ordered : Prop where
  /-- `d'_{p,i} ≤ d_{p,i}`. -/
  longEarly_le : ∀ i, A.longEarly i ≤ A.longDue i
  /-- `d_{p,i} ≤ d'_{p,i+1}`. -/
  longDue_le : ∀ i j : Fin A.pairs, (i : ℕ) + 1 = j → A.longDue i ≤ A.longEarly j
  /-- `d'_{q,i} ≤ d_{q,i}`. -/
  shortEarly_le : ∀ i, A.shortEarly i ≤ A.shortDue i
  /-- `d_{q,i} ≤ d'_{q,i+1}`. -/
  shortDue_le : ∀ i j : Fin A.pairs, (i : ℕ) + 1 = j → A.shortDue i ≤ A.shortEarly j
  /-- `d_{p,i} ≤ d'_{q,i}`. -/
  longDue_le_shortEarly : ∀ i, A.longDue i ≤ A.shortEarly i

variable {A}

variable (A)

end Instance

end Lax391470.AuxiliaryProblem
end

-- Lax391470.StackedConstruction
section
namespace Lax391470.StackedConstruction

open Lax391470.Scheduling Lax391470.AuxiliaryProblem

variable (p q : ℕ) (A : AuxiliaryProblem.Instance)

/-- The left end `tᵢ` of the bin of pair `i`, pairs counted from `0`. -/
def binStart (i : ℕ) : ℤ := -(((p + 2 * q) * (i + 1) : ℕ) : ℤ)

/-- The number of jobs: the ordinary ones and five for every connected pair. -/
def numJobs : ℕ := A.ordinary + 5 * A.pairs

/-- The pair a job beyond the ordinary ones belongs to. -/
def pairOf (j : ℕ) : ℕ := (j - A.ordinary) / 5

/-- Which of the five jobs of its pair a job is: `0` the separator, `1` the inner long
job, `2` the outer long job, `3` the inner short job, `4` the outer short job. -/
def partOf (j : ℕ) : ℕ := (j - A.ordinary) % 5

/-- **The stacked instance** built from `A` at the lengths `p` and `q`. -/
def inst : Scheduling.Instance where
  jobs := numJobs A
  r j :=
    if h : (j : ℕ) < A.ordinary then A.r ⟨j, h⟩
    else
      binStart p q (pairOf A j) +
        match partOf A j with
        | 0 => (p + q : ℕ)
        | 1 => (q : ℕ)
        | 2 => 0
        | 3 => (p : ℕ)
        | _ => 0
  d j :=
    if h : (j : ℕ) < A.ordinary then A.d ⟨j, h⟩
    else
      have hi : pairOf A j < A.pairs := by
        have := j.isLt
        simp only [pairOf, numJobs] at *
        omega
      match partOf A j with
      | 0 => binStart p q (pairOf A j) + (p + 2 * q : ℕ)
      | 1 => A.longEarly ⟨pairOf A j, hi⟩
      | 2 => A.longDue ⟨pairOf A j, hi⟩
      | 3 => A.shortEarly ⟨pairOf A j, hi⟩
      | _ => A.shortDue ⟨pairOf A j, hi⟩
  p j :=
    if h : (j : ℕ) < A.ordinary then (if A.long ⟨j, h⟩ then p else q)
    else
      match partOf A j with
      | 1 => p
      | 2 => p
      | _ => q

/-- **The numbers of the stacked instance are small**: if every release time and every
deadline of an ordered instance `A` is at most `T`, every release time and deadline of the
stacked instance lies within `T + (p + 2q)N` of `0`, where `N` is the number of pairs.
Together with `SatConstruction.times_le`, this bounds every number of the composed
reduction by a polynomial in the size of the formula. -/
axiom times_le (hA : A.Ordered) (T : ℕ)
    (hT : (∀ o, A.r o ≤ T ∧ A.d o ≤ T) ∧
      (∀ i, A.longDue i ≤ T ∧ A.shortDue i ≤ T)) :
    ∀ j, |(inst p q A).r j| ≤ ((T + (p + 2 * q) * A.pairs : ℕ) : ℤ) ∧
      |(inst p q A).d j| ≤ ((T + (p + 2 * q) * A.pairs : ℕ) : ℤ)

end Lax391470.StackedConstruction
end
