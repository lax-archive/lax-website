-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax9.MergeWidth
section
namespace Lax9.MergeWidth

open scoped Classical

universe u

variable {V : Type u} [Fintype V]

namespace MergeSeq

variable {G : SimpleGraph V}

end MergeSeq

/-- A **graph class**: a property of finite simple graphs. -/
def GraphClass : Type 1 := ∀ ⦃V : Type⦄ [Fintype V], SimpleGraph V → Prop

end Lax9.MergeWidth
end

-- Lax9.NeighborhoodComplexity
section
namespace Lax9.NeighborhoodComplexity

open Lax9.MergeWidth

open scoped Classical

universe u

variable {V : Type u} [Fintype V]

/-- The neighbourhood complexity $π_G(p)$ of a finite simple graph $G$. -/
noncomputable def neighborhoodComplexity (G : SimpleGraph V) (p : ℕ) : ℕ :=
  (Finset.univ.powersetCard p).sup fun X =>
    ((Finset.univ \ X).image fun v => X.filter fun u => G.Adj v u).card

/-- A graph class has linear neighbourhood complexity if $π_G(p) ≤ c p$ for
some constant $c$ and every positive $p$. -/
def LinearNeighborhoodComplexity (C : GraphClass) : Prop :=
  ∃ c : ℕ, ∀ ⦃V : Type⦄ [Fintype V] (G : SimpleGraph V), C G → ∀ p, 1 ≤ p →
    neighborhoodComplexity G p ≤ c * p

end Lax9.NeighborhoodComplexity
end
