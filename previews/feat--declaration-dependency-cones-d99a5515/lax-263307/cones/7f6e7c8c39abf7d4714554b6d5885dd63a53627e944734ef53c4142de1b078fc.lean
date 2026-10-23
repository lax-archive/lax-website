-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Basic

-- Lax263307.WidthGrowth
section
namespace Lax263307.WidthGrowth

def threshold (a A c : ℕ) : ℕ := (12 * c) ^ a * A * (6 * (24 * c) ^ 2 + 1) ^ (a - 1)

axiom order_bound (a A c ℓ t m q : ℕ) (a_positive : 0 < a) (ℓ_positive : 0 < ℓ)
    (t_positive : 0 < t) (W : ℕ → ℕ)
    (W_positive : ∀ M, 1 ≤ W M) (W_power : ∀ M, (W M) ^ a ≤ A * (M + 1) ^ (a - 1))
    (edges : m ≤ 2 * t) (discarded : (24 * c * ℓ) * q ≤ 4 * m * ℓ)
    (width : t ≤ c * (max 1 (6 * W (3 * m * (24 * c * ℓ) ^ 2)) + q)) :
    t ≤ threshold a A c * ℓ ^ (2 * (a - 1))

end Lax263307.WidthGrowth
end
