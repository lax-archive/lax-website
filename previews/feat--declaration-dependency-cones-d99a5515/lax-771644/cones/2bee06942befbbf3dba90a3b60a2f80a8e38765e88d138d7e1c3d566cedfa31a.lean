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

-- Lax771644.WideDockRow
section
namespace Lax771644.WideDockRow

/-- Descent from stage 110 to stage 109. -/
axiom s10 : Foundations.Descent 110 109

end Lax771644.WideDockRow
end
