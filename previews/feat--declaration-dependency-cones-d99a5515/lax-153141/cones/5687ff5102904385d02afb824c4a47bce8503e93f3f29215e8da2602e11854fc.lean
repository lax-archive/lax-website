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

end Lax153141.GraphParameters
end
