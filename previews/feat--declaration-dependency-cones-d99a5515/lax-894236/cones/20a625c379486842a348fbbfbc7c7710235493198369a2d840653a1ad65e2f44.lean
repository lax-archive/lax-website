-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Choose.Basic

-- Lax894236.GeometricGenus
section
namespace Lax894236
end Lax894236

namespace Lax894236.GeometricGenus
end Lax894236.GeometricGenus
end

-- Lax894236.NoetherLefschetzWindow
section
namespace Lax894236.NoetherLefschetzWindow

open Lax894236.GeometricGenus

/-- Six times the window `p_g − (d − 3)` is `(d−4)(d−3)(d+1)`, six times
`A005581(d−3)`, for every integer `d`. -/
axiom window_eq_A005581 (d : ℤ) :
    (d - 1) * (d - 2) * (d - 3) - 6 * (d - 3) = (d - 4) * (d - 3) * (d + 1)

end Lax894236.NoetherLefschetzWindow
end
