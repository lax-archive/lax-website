-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax49.GraphParameters
section
namespace Lax49.GraphParameters

/-- A natural-valued parameter of finite simple graphs, in the uniform
signature shared by all graph parameters in this archive. -/
abbrev GraphParam :=
  ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → ℕ

end Lax49.GraphParameters
end
