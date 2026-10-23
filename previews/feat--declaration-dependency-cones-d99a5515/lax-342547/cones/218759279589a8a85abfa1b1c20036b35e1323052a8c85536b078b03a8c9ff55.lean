-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

-- Lax342547.ContainerAsymptotics
section
namespace Lax342547.ContainerAsymptotics

open Filter Asymptotics

def exponentBudget (A g N : ℕ) : ℕ := (2*A*N^2+1)*(4000*g*N*2^(100*g*N)+2)

axiom eventually_container_exponent (A g : ℕ) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop, exponentBudget A g N+2 < 2^(1000*g*N)

end Lax342547.ContainerAsymptotics
end
