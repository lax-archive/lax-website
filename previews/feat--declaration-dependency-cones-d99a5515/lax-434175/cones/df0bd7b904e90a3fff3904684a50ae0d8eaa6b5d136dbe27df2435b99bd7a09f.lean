-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs

-- Lax434175.Kernels
section
namespace Lax434175.Kernels

/-- A machine model: instances, schedules, and the accessors through which
constraints and objectives read a schedule. -/
structure Kernel where
  /-- The instances of the machine model. -/
  Inst : Type
  /-- The number of jobs of an instance. -/
  jobs : Inst → ℕ
  /-- The release date of a job. -/
  release : (x : Inst) → Fin (jobs x) → ℕ
  /-- The schedules of an instance. -/
  Sched : Inst → Type
  /-- The feasibility conditions of the machine model itself. -/
  feasible : (x : Inst) → Sched x → Prop
  /-- The time at which a job starts. -/
  start : (x : Inst) → Sched x → Fin (jobs x) → NNRat
  /-- The time at which a job completes. -/
  completion : (x : Inst) → Sched x → Fin (jobs x) → NNRat

end Lax434175.Kernels
end

-- Lax434175.Modules
section
namespace Lax434175.Modules.Objective
end Lax434175.Modules.Objective

namespace Lax434175.Modules.Objective.Sound
end Lax434175.Modules.Objective.Sound

namespace Lax434175.Modules

open Lax434175.Kernels

/-- A field whose values add data to an instance and a constraint on its
schedules. -/
structure Module (K : Kernel) where
  Value : Type
  /-- The data a value adds to an instance. -/
  Data : Value → K.Inst → Type
  /-- The condition a value imposes on an instance and its data. -/
  admits : (v : Value) → (x : K.Inst) → Data v x → Prop
  /-- The constraint a value imposes on the schedules. -/
  constraint : (v : Value) → (x : K.Inst) → Data v x → K.Sched x → Prop
  /-- `le v w`: the value `v` is a special case of `w`. -/
  le : Value → Value → Bool
  /-- Data of a value read as data of a more general value. -/
  embed : {v w : Value} → le v w = true → (x : K.Inst) → Data v x → Data w x

/-- Reading data with a more general value keeps it admissible and does not
change the constraint. -/
structure Module.Sound {K : Kernel} (M : Module K) : Prop where
  admits : ∀ (v w : M.Value) (h : M.le v w = true) (x : K.Inst) (d : M.Data v x),
    M.admits v x d → M.admits w x (M.embed h x d)
  constraint : ∀ (v w : M.Value) (h : M.le v w = true) (x : K.Inst) (d : M.Data v x)
    (σ : K.Sched x), M.admits v x d →
      (M.constraint w x (M.embed h x d) σ ↔ M.constraint v x d σ)

end Lax434175.Modules
end

-- Lax434175.ReleaseDates
section
namespace Lax434175.ReleaseDates

open Lax434175.Kernels Lax434175.Modules

inductive Value
  | none
  | releaseDates
  | online
  deriving DecidableEq

/-- The instances of a value. -/
def Value.holds (K : Kernel) : Value → K.Inst → Prop
  | .none, x => ∀ j, K.release x j = 0
  | .releaseDates, _ => True
  | .online, _ => True

def le : Value → Value → Bool
  | .none, .releaseDates => true
  | v, w => decide (v = w)

/-- The release-date field over a kernel. -/
def module (K : Kernel) : Module K where
  Value := Value
  Data _ _ := Unit
  admits v x _ := v.holds K x
  constraint _ x _ σ := ∀ j, (K.release x j : NNRat) ≤ K.start x σ j
  le := le
  embed _ _ _ := ()

axiom sound (K : Kernel) : (module K).Sound

end Lax434175.ReleaseDates
end
