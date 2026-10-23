-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d



-- Lax755887.MergeCost
section
namespace Lax755887.MergeCost

axiom linearMergeCost : ∃ C : Nat, ∀ k : Nat, k * 2 ^ k ≤ C * 2 ^ k

end Lax755887.MergeCost
end
