-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2

-- Lax14.MulticolorRamsey
section
namespace Lax14.MulticolorRamsey

/-- Ramsey's theorem for pairs: every `k`-colouring of the unordered pairs
of a large enough finite set has a monochromatic subset of size `s`. -/
axiom exists_monochromatic_set (k s : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (c : Sym2 (Fin n) → Fin k), N ≤ n →
      ∃ (i : Fin k) (S : Set (Fin n)), s ≤ S.ncard ∧
        S.Pairwise fun u v => c s(u, v) = i

end Lax14.MulticolorRamsey
end
