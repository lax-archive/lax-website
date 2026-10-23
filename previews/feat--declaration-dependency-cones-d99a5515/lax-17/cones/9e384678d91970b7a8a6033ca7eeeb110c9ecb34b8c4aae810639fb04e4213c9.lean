-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d



-- Lax17.PowerRoot
section
namespace Lax17.PowerRoot

/-- `rho` is the least natural number satisfying $g^2 \leq \rho^t$. -/
def IsCeilingPowerRoot (t g rho : Nat) : Prop :=
  g ^ 2 ≤ rho ^ t ∧
    ∀ a : Nat, a < rho → a ^ t < g ^ 2

end Lax17.PowerRoot
end
