-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

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
