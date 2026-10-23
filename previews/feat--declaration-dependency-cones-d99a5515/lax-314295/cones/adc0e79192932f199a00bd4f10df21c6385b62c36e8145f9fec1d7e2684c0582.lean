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

/-- Extend a valuation of the set variables `0, …, l-1` to all variables. -/
def extSO (l : ℕ) (so : Fin l → Set ℕ) : ℕ → Set ℕ :=
  fun j => if h : j < l then so ⟨j, h⟩ else ∅

end Lax314295.MSOLogic
end
