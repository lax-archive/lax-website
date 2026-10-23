-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

-- Lax3.ColoredGraphs
section
namespace Lax3.ColoredGraphs

/-- A coloring of the vertices `Fin n` by `L` colors: one set of
vertices per color. Colors need be neither disjoint nor covering, so a
vertex may carry any set of colors. -/
abbrev Coloring (n L : ℕ) : Type := Fin L → Set (Fin n)

end Lax3.ColoredGraphs
end
