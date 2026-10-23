-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

-- Lax496464.WordEncoding
section
namespace Lax496464.WordEncoding

open Lax496464.FlowShop Lax496464.FlowShop.Instance

/-- The number of jobs declared by a word: its first entry. -/
def jobCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of machines declared by a word: its second entry. -/
def machineCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The preprocessing time of job `j`, from the block following the two header
entries. -/
def preTime (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + j) 0

/-- The processing time of job `j`, from the block following the preprocessing times. -/
def procTime (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + jobCount x + j) 0

/-- The due date of job `j`, from the block following the processing times. -/
def due (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + 2 * jobCount x + j) 0

/-- The weight of job `j`, from the block following the due dates. -/
def wt (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + 3 * jobCount x + j) 0

/-- The word `x` encodes the instance `I`. -/
structure EncodesInstance (x : List ℕ) (I : Instance) : Prop where
  /-- The word declares `I`'s jobs. -/
  jobCount_eq : jobCount x = I.jobs
  /-- The word declares `I`'s machines. -/
  machineCount_eq : machineCount x = I.machines
  /-- The word is the two header entries followed by four blocks of one number per job. -/
  length_eq : x.length = 2 + 4 * I.jobs
  /-- The preprocessing times are `I`'s. -/
  preTime_eq : ∀ j : I.Job, preTime x j = I.p j
  /-- The processing times are `I`'s. -/
  procTime_eq : ∀ j : I.Job, procTime x j = I.q j
  /-- The due dates are `I`'s. -/
  due_eq : ∀ j : I.Job, due x j = I.d j
  /-- The weights are `I`'s. -/
  wt_eq : ∀ j : I.Job, wt x j = I.w j

/-- The word `x` presents the instance `I` together with the threshold `W`: an instance
block followed by the single entry `W`. -/
def EncodesDecisionInstance (x : List ℕ) (I : Instance) (W : ℕ) : Prop :=
  ∃ y, x = y ++ [W] ∧ EncodesInstance y I

/-- The words that encode a decision instance. -/
def DecisionInstances : Set (List ℕ) := {x | ∃ I W, EncodesDecisionInstance x I W}

end Lax496464.WordEncoding
end
