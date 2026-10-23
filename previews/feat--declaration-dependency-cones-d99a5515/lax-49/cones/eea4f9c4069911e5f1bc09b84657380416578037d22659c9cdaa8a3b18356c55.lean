-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

-- Lax49.MixedMinorNumber
section
namespace Lax49.MixedMinorNumber

/-- A division of `Fin n` into `k` nonempty consecutive intervals in
increasing order. Disjointness and convexity of the parts follow from
`part_ordered` and `part_cover`. -/
structure Division (n k : ℕ) where
  /-- The `i`-th part of the division. -/
  part : Fin k → Finset (Fin n)
  /-- Every part is nonempty. -/
  part_nonempty : ∀ i, (part i).Nonempty
  /-- The parts cover the whole interval. -/
  part_cover : ∀ x : Fin n, ∃ i, x ∈ part i
  /-- Earlier-indexed parts lie strictly before later-indexed parts. -/
  part_ordered :
    ∀ ⦃i j : Fin k⦄, i < j →
      ∀ ⦃a b : Fin n⦄, a ∈ part i → b ∈ part j → a < b

/-- A matrix cell is horizontal when each row is constant within the column
part. -/
def cellHorizontal {n m k : ℕ} (M : Fin n → Fin m → Prop)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ R.part i →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C.part j → c₂ ∈ C.part j →
      (M r c₁ ↔ M r c₂)

end Lax49.MixedMinorNumber
end
