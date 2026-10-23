-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

-- Lax606786.MeasurableSelection
section
namespace Lax606786.MeasurableSelection

/-- The first index of a countable measurable cover is measurable. -/
axiom measurable_of_countable_cover {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (x : ℕ → Y) (S : ℕ → Set Ω) (hS : ∀ n, MeasurableSet (S n)) (hcover : (⋃ n, S n) = Set.univ) :
    ∃ N : Ω → ℕ, Measurable N ∧ Measurable (fun ω => x (N ω)) ∧
      ∀ ω, ω ∈ S (N ω) ∧ ∀ m, ω ∈ S m → N ω ≤ m

end Lax606786.MeasurableSelection
end
