-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Basic

-- Lax263307.WidthGrowth
section
namespace Lax263307.WidthGrowth

def threshold (a A c : ℕ) : ℕ := (12 * c) ^ a * A * (6 * (24 * c) ^ 2 + 1) ^ (a - 1)

end Lax263307.WidthGrowth
end
