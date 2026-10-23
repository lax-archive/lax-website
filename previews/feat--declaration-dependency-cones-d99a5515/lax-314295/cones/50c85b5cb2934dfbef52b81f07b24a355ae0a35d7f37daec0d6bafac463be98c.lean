-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Basic

-- Lax314295.MSOLogic
section
namespace Lax314295.MSOLogic.MSO.IsFO
end Lax314295.MSOLogic.MSO.IsFO

namespace Lax314295.MSOLogic.MSO.Sat
end Lax314295.MSOLogic.MSO.Sat

namespace Lax314295.MSOLogic.MSO.and
end Lax314295.MSOLogic.MSO.and

namespace Lax314295.MSOLogic.MSO.exFO
end Lax314295.MSOLogic.MSO.exFO

namespace Lax314295.MSOLogic.MSO.exSO
end Lax314295.MSOLogic.MSO.exSO

namespace Lax314295.MSOLogic.MSO.lab
end Lax314295.MSOLogic.MSO.lab

namespace Lax314295.MSOLogic.MSO.le
end Lax314295.MSOLogic.MSO.le

namespace Lax314295.MSOLogic.MSO.mem
end Lax314295.MSOLogic.MSO.mem

namespace Lax314295.MSOLogic.MSO.not
end Lax314295.MSOLogic.MSO.not

namespace Lax314295.MSOLogic.MSO.or
end Lax314295.MSOLogic.MSO.or

namespace Lax314295.MSOLogic

namespace MSO

variable {A : Type}

end MSO

open scoped Classical in
/-- The annotation `w ⊗ {x₁} ⊗ ⋯ ⊗ {x_k} ⊗ X₁ ⊗ ⋯ ⊗ X_l` of a string by the values
of `k` first-order and `l` second-order variables. -/
noncomputable def annotate {A : Type} (k l : ℕ) (w : List A)
    (fo : Fin k → ℕ) (so : Fin l → Set ℕ) : List (A × (Fin k → Bool) × (Fin l → Bool)) :=
  w.zipIdx.map (fun z => (z.1, fun i => decide (fo i = z.2), fun j => decide (z.2 ∈ so j)))

end Lax314295.MSOLogic
end
