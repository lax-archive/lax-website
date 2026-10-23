-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Logic.Embedding.Basic
import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Semantics

-- Lax12.GraphClasses
section
namespace Lax12.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax12.GraphClasses
end

-- Lax5.GraphClasses
section
namespace Lax5
end Lax5

namespace Lax5.GraphClasses
end Lax5.GraphClasses
end

-- Lax5.Transductions
section
namespace Lax5.Transductions.ColorRel
end Lax5.Transductions.ColorRel

namespace Lax5.Transductions.Transduction
end Lax5.Transductions.Transduction

namespace Lax5.Transductions.colorStructure
end Lax5.Transductions.colorStructure

namespace Lax5.Transductions.ColorRel.color
end Lax5.Transductions.ColorRel.color

namespace Lax5.Transductions

open FirstOrder

universe u v u' v'

/-- A class of finite structures of the language `L`: for each `n`, a
predicate on the `L`-structures over the canonical `n`-element type. -/
abbrev StructureClass (L : Language.{u, v}) : Type (max u v) :=
  ∀ n : ℕ, L.Structure (Fin n) → Prop

end Lax5.Transductions
end

-- Lax5.GraphTransductions
section
namespace Lax5.GraphTransductions

open FirstOrder Lax12.GraphClasses

/-- The members of a graph class, as structures of the language of
graphs: adjacency interprets the binary relation. -/
def structureClass (C : GraphClass) :
    Transductions.StructureClass Language.graph :=
  fun n S => ∃ G : SimpleGraph (Fin n), C n G ∧ S = G.structure

end Lax5.GraphTransductions
end
