-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

-- Lax871432.Contractions
section
namespace Lax871432.Contractions

/-- A presentation of `K` as the graph obtained from `F` by contracting the edges inside the
classes of a partition of `V(F)` into connected parts. -/
structure Contraction {V W : Type*} (K : SimpleGraph W) (F : SimpleGraph V) where
  /-- The vertex of `K` a vertex of `F` is contracted to. -/
  proj : V → W
  /-- Each class induces a connected — in particular nonempty — subgraph of `F`. -/
  connected : ∀ w, (F.induce {v | proj v = w}).Connected
  /-- Distinct classes are adjacent in `K` exactly when `F` joins them. -/
  adj_iff : ∀ a b, K.Adj a b ↔ a ≠ b ∧ ∃ x y, F.Adj x y ∧ proj x = a ∧ proj y = b

end Lax871432.Contractions
end
