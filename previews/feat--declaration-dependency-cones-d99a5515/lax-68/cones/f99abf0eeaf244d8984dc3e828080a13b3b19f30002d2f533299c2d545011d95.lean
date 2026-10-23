-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.UniversalVerts

-- Lax68.Stars
section
set_option autoImplicit false

namespace Lax68.Stars

def HasStarShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ centre : V,
    centre ∈ G.universalVerts ∧
    ∀ ⦃u v⦄, G.Adj u v → u = centre ∨ v = centre

def IsStar {V : Type*} (G : SimpleGraph V) : Prop :=
  HasStarShape G

end Lax68.Stars
end

-- Lax68.Trees
section
set_option autoImplicit false

namespace Lax68.Trees

def IsTree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsTree

end Lax68.Trees
end

-- Lax68.StarTree
section
set_option autoImplicit false

namespace Lax68.StarTree

/-- Every star graph is a tree. -/
axiom star_tree {V : Type*} {G : SimpleGraph V} :
  Lax68.Stars.IsStar G →
  Lax68.Trees.IsTree G

end Lax68.StarTree
end
