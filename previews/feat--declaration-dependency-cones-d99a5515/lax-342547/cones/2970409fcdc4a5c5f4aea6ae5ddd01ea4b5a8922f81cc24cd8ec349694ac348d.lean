-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Union
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.Conditioning
section
namespace Lax342547.Conditioning

open scoped ENNReal

axiom disjoint_mixture {Ω J : Type} [DecidableEq Ω] (p : PMF Ω)
    (L : Finset J) (S : J → Finset Ω)
    (hdisjoint : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → Disjoint (S i) (S j))
    (hS : ∀ j ∈ L, ∃ o ∈ (S j : Set Ω), o ∈ p.support) (o : Ω) :
    (∑ j : {j // j ∈ L}, p.toOuterMeasure (S j.val) * (p.filter (S j.val) (hS j.val j.property)) o) =
      (L.biUnion S : Set Ω).indicator p o

end Lax342547.Conditioning
end
