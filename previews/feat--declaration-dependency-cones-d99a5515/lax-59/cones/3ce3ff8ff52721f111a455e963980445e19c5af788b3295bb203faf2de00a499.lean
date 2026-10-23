-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib

-- Lax59.Nagura
section
namespace Lax59.Nagura

/-- The natural-number form of Nagura's prime-interval property. -/
def NaguraBound : Prop :=
  ∀ x : ℕ, 25 ≤ x → ∃ r : ℕ, r.Prime ∧ x < r ∧ 5 * r < 6 * x

/-- Nagura's theorem in the natural-number form used by this submission. -/
axiom nagura_bound : NaguraBound

end Lax59.Nagura
end
