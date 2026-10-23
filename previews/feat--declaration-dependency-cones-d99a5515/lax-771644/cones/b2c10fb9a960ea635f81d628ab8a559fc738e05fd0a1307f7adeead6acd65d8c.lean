-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Notation

-- Lax771644.Foundations
section
namespace Lax771644.Foundations

/-- `Stage k n` says that `n` is divisible by `2 ^ k`. -/
def Stage (k n : ℕ) : Prop := 2 ^ k ∣ n

/-- `Descent a b` is the one statement shape this submission uses: every natural
number divisible by `2 ^ a` is divisible by `2 ^ b`. -/
def Descent (a b : ℕ) : Prop := ∀ n : ℕ, Stage a n → Stage b n

end Lax771644.Foundations
end

-- Lax771644.CycleAlpha
section
namespace Lax771644.CycleAlpha

/-- Descent from stage 300 to stage 290. -/
axiom alpha : Foundations.Descent 300 290

end Lax771644.CycleAlpha
end
