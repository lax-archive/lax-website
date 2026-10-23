-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2

-- Lax345067.MulticolorRamsey
section
namespace Lax345067.MulticolorRamsey

/-- Ramsey's theorem for pairs: every `k`-colouring of the unordered pairs
of a large enough finite set has a monochromatic subset of size `s`. -/
axiom exists_monochromatic_set (k s : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (c : Sym2 (Fin n) → Fin k), N ≤ n →
      ∃ (i : Fin k) (S : Set (Fin n)), s ≤ S.ncard ∧
        S.Pairwise fun u v => c s(u, v) = i

end Lax345067.MulticolorRamsey
end
