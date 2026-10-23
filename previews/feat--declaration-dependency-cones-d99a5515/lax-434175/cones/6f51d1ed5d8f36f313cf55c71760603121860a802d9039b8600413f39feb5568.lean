-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

namespace Lax434175.Modules.Module.Sound
end Lax434175.Modules.Module.Sound

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

end Lax434175.Modules
end

-- Lax434175.ForbiddenTimes
section
namespace Lax434175.ForbiddenTimes.Encoding
end Lax434175.ForbiddenTimes.Encoding

namespace Lax434175.ForbiddenTimes.Encoding.highMultiplicity
end Lax434175.ForbiddenTimes.Encoding.highMultiplicity

namespace Lax434175.ForbiddenTimes.Encoding.standard
end Lax434175.ForbiddenTimes.Encoding.standard

namespace Lax434175.ForbiddenTimes

open Lax434175.Kernels Lax434175.Modules

inductive Value
  | none
  | forbidden

/-- No data without forbidden times; a list of points in time with them. -/
def Data : Value → Type
  | .none => Unit
  | .forbidden => List ℕ

/-- The forbidden times; none when the field is absent. -/
def view : (v : Value) → Data v → List ℕ
  | .none, _ => []
  | .forbidden, l => l

def le : Value → Value → Bool
  | .forbidden, .none => false
  | _, _ => true

def embed : {v w : Value} → le v w = true → Data v → Data w
  | _, .none, _, _ => ()
  | v, .forbidden, _, d => view v d

/-- The forbidden-times field over a kernel. -/
def module (K : Kernel) : Module K where
  Value := Value
  Data v _ := Data v
  admits _ _ _ := True
  constraint v x d σ := ∀ t ∈ view v d, ∀ j,
    K.start x σ j ≠ (t : NNRat) ∧ K.completion x σ j ≠ (t : NNRat)
  le := le
  embed h _ d := embed h d

end Lax434175.ForbiddenTimes
end
