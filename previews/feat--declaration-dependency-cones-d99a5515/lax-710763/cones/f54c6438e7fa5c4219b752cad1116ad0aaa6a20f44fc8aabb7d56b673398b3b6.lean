-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Logic.Embedding.Basic
import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Semantics

-- Lax199508.GraphClasses
section
namespace Lax199508.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax199508.GraphClasses
end

-- Lax710763.GraphClasses
section
namespace Lax710763
end Lax710763

namespace Lax710763.GraphClasses
end Lax710763.GraphClasses
end

-- Lax710763.Transductions
section
namespace Lax710763.Transductions.ColorRel
end Lax710763.Transductions.ColorRel

namespace Lax710763.Transductions.Transduction
end Lax710763.Transductions.Transduction

namespace Lax710763.Transductions.colorStructure
end Lax710763.Transductions.colorStructure

namespace Lax710763.Transductions.ColorRel.color
end Lax710763.Transductions.ColorRel.color

namespace Lax710763.Transductions

open FirstOrder

universe u v u' v'

/-- A class of finite structures of the language `L`: for each `n`, a
predicate on the `L`-structures over the canonical `n`-element type. -/
abbrev StructureClass (L : Language.{u, v}) : Type (max u v) :=
  ∀ n : ℕ, L.Structure (Fin n) → Prop

end Lax710763.Transductions
end

-- Lax710763.GraphTransductions
section
namespace Lax710763.GraphTransductions

open FirstOrder Lax199508.GraphClasses

/-- The members of a graph class, as structures of the language of
graphs: adjacency interprets the binary relation. -/
def structureClass (C : GraphClass) :
    Transductions.StructureClass Language.graph :=
  fun n S => ∃ G : SimpleGraph (Fin n), C n G ∧ S = G.structure

end Lax710763.GraphTransductions
end
