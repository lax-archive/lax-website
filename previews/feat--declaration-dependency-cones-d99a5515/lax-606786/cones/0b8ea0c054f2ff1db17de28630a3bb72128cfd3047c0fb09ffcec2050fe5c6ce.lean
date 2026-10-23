-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Lax606786.ExtendedLog
section
namespace Lax606786.ExtendedLog

/-- `log r` for `r > 0`, and `-∞` for `r ≤ 0`. -/
noncomputable def logEReal (r : ℝ) : EReal := if r ≤ 0 then ⊥ else (Real.log r : EReal)

end Lax606786.ExtendedLog
end
