-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax323828.BooleanFourier
section
namespace Lax323828.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def character {ι : Type} (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, sign (x i)

noncomputable def average {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) : ℝ :=
  (∑ x, F x) / (2 : ℝ) ^ Fintype.card ι

noncomputable def coefficient {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ)
    (S : Finset ι) : ℝ :=
  average fun x ↦ F x * character S x

end Lax323828.BooleanFourier
end

-- Lax323828.FourierProjection
section
namespace Lax323828.FourierProjection

open BooleanFourier

def splice {ι : Type} [DecidableEq ι] (U : Finset ι) (x y : Cube ι) : Cube ι :=
  fun i ↦ if i ∈ U then x i else y i

noncomputable def project {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (U : Finset ι) (x : Cube ι) : ℝ :=
  average fun y ↦ F (splice U x y)

end Lax323828.FourierProjection
end

-- Lax323828.SmallSupport
section
namespace Lax323828.SmallSupport

open scoped Classical

/-- The coordinate sets of size at most `l` whose squared coefficient is at least `l * δ`. -/
noncomputable def largeSets {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset (Finset ι) :=
  Finset.univ.filter fun a ↦ a.card ≤ l ∧ (l : ℝ) * δ ≤ c a ^ 2

/-- The union of the coordinate sets selected by `largeSets`. -/
noncomputable def decodingSet {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset ι :=
  (largeSets c l δ).biUnion id

end Lax323828.SmallSupport
end

-- Lax323828.FourierDecoding
section
namespace Lax323828.FourierDecoding

open BooleanFourier FourierProjection SmallSupport

axiom projected_decoding_subset {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (U : Finset ι) (l : ℕ) (δ : ℝ) (hδ : 0 < δ) :
  decodingSet (coefficient (project F U)) l δ ⊆ decodingSet (coefficient F) l δ ∩ U

end Lax323828.FourierDecoding
end
