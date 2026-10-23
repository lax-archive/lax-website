-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.PartrecCode

-- Lax251941.Acceptance
section
namespace Lax251941.Acceptance

/-- A machine: a partial recursive program. -/
abbrev Machine := Nat.Partrec.Code

/-- `M` rejects `w` if it halts on `w` with output `0`. -/
def Rejects (M : Machine) (w : ℕ) : Prop := M.eval w = Part.some 0

end Lax251941.Acceptance
end
