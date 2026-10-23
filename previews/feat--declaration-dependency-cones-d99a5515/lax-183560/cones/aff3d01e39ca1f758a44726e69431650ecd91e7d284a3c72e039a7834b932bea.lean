-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Lattice.Nat

-- Lax183560.AncestorForest
section
namespace Lax183560.AncestorForest

/-- A strict ancestor relation of a rooted forest on `V`. -/
structure AncestorForest (V : Type) where
  ancestor : V → V → Prop
  transitive : IsTrans V ancestor
  irreflexive : Std.Irrefl ancestor
  ancestors_linearly_ordered : ∀ u v w : V,
    (ancestor u w ∧ ancestor v w) → (u = v ∨ ancestor u v ∨ ancestor v u)

end Lax183560.AncestorForest
end

-- Lax183560.TreeDepth
section
namespace Lax183560.TreeDepth

open Lax183560.AncestorForest

/-- `G` lies in the closure of a forest of vertex height at most `k`. -/
def HasTreedepthAtMost {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ F : AncestorForest V,
    (∀ ⦃u v : V⦄, G.Adj u v → (F.ancestor u v ∨ F.ancestor v u)) ∧
    ∃ rank : V → Fin k,
      ∀ ⦃u v : V⦄, F.ancestor u v → rank u < rank v

/-- The minimum height of a rooted forest whose closure contains `G`. -/
noncomputable def treedepth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k | HasTreedepthAtMost G k}

end Lax183560.TreeDepth
end
