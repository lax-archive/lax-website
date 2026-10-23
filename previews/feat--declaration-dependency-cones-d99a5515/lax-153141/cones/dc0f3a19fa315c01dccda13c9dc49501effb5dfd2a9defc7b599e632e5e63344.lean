-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax153141.GraphParameters
section
namespace Lax153141.GraphParameters

/-- A natural-valued parameter of finite simple graphs, in the uniform
signature shared by all graph parameters in this archive. -/
abbrev GraphParam :=
  ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → ℕ

/-- Each of two graph parameters is bounded by a numerical function of the
other. -/
def FunctionallyEquivalent (p q : GraphParam) : Prop :=
  (∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V), p G ≤ f (q G)) ∧
  (∃ g : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V), q G ≤ g (p G))

end Lax153141.GraphParameters
end
