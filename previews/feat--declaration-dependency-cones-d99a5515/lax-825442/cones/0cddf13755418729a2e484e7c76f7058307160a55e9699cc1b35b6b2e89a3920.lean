-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Computability.Partrec
import Mathlib.Order.Monotone.Basic

-- Lax153141.GraphParameters
section
namespace Lax153141.GraphParameters

/-- A natural-valued parameter of finite simple graphs, in the uniform
signature shared by all graph parameters in this archive. -/
abbrev GraphParam :=
  ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → ℕ

end Lax153141.GraphParameters
end

-- Lax825442.Bounds
section
namespace Lax825442.Bounds

open Lax153141.GraphParameters

/-- A computable nondecreasing function of `p` bounds `q` on every finite simple graph. -/
def Bounds (p q : GraphParam) : Prop :=
  ∃ f : ℕ → ℕ, Computable f ∧ Monotone f ∧
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      q G ≤ f (p G))

end Lax825442.Bounds
end

-- Lax825442.Equivalent
section
namespace Lax825442.Equivalent

open Lax153141.GraphParameters

/-- Functional bounds hold in both directions. -/
def Equivalent (p q : GraphParam) : Prop :=
  (Lax825442.Bounds.Bounds p q) ∧ (Lax825442.Bounds.Bounds q p)

end Lax825442.Equivalent
end
