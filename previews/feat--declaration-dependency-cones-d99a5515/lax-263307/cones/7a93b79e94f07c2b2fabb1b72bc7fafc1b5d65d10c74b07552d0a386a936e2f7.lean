-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.DeriveFintype

-- Lax560851.StructuralPresentation
section
namespace Lax560851
end Lax560851

namespace Lax560851.StructuralPresentation
end Lax560851.StructuralPresentation

namespace Lax560851.StructuralPresentation.Presentation
end Lax560851.StructuralPresentation.Presentation

namespace Lax560851.StructuralPresentation.Raw
end Lax560851.StructuralPresentation.Raw

namespace Lax560851.StructuralPresentation.Raw.nat
end Lax560851.StructuralPresentation.Raw.nat

namespace Lax560851.StructuralPresentation.Raw.nodes
end Lax560851.StructuralPresentation.Raw.nodes

namespace Lax560851.StructuralPresentation.Raw.pair
end Lax560851.StructuralPresentation.Raw.pair
end

-- Lax560851.WordArena
section
namespace Lax560851.WordArena
end Lax560851.WordArena

namespace Lax560851.WordArena.WordImage
end Lax560851.WordArena.WordImage

namespace Lax560851.WordArena.encodeInto
end Lax560851.WordArena.encodeInto

namespace Lax560851.WordArena.WordImage.ChildAddress
end Lax560851.WordArena.WordImage.ChildAddress

namespace Lax560851.WordArena.WordImage.ReachableFrom
end Lax560851.WordArena.WordImage.ReachableFrom

namespace Lax560851.WordArena.WordImage.Represents
end Lax560851.WordArena.WordImage.Represents
end

-- Lax759944.BinaryWordEncoding
section
namespace Lax759944
end Lax759944

namespace Lax759944.BinaryWordEncoding
end Lax759944.BinaryWordEncoding

namespace Lax759944.BinaryWordEncoding.Symbol
end Lax759944.BinaryWordEncoding.Symbol

namespace Lax759944.BinaryWordEncoding.Symbol.one
end Lax759944.BinaryWordEncoding.Symbol.one

namespace Lax759944.BinaryWordEncoding.Symbol.separator
end Lax759944.BinaryWordEncoding.Symbol.separator

namespace Lax759944.BinaryWordEncoding.Symbol.zero
end Lax759944.BinaryWordEncoding.Symbol.zero
end

-- Lax213208.OptimizationProblem
section
namespace Lax213208
end Lax213208

namespace Lax213208.OptimizationProblem
end Lax213208.OptimizationProblem

namespace Lax213208.OptimizationProblem.Direction
end Lax213208.OptimizationProblem.Direction

namespace Lax213208.OptimizationProblem.Problem
end Lax213208.OptimizationProblem.Problem

namespace Lax213208.OptimizationProblem.Direction.maximize
end Lax213208.OptimizationProblem.Direction.maximize

namespace Lax213208.OptimizationProblem.Direction.minimize
end Lax213208.OptimizationProblem.Direction.minimize
end

-- Lax263307.GraphClasses
section
namespace Lax263307.GraphClasses

/-- A class of finite simple graphs, represented on numbered vertex sets. -/
abbrev GraphClass := (n : ℕ) → Set (SimpleGraph (Fin n))

end Lax263307.GraphClasses
end

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307.WeightedIndependentSet

/-- A finite graph with rational vertex weights. -/
structure Instance where
  order : ℕ
  graph : SimpleGraph (Fin order)
  weights : Fin order → ℚ

end Lax263307.WeightedIndependentSet
end

-- Lax560851.StructuralCombinators
section
namespace Lax560851.StructuralCombinators
end Lax560851.StructuralCombinators

namespace Lax560851.StructuralCombinators.Derivable
end Lax560851.StructuralCombinators.Derivable

namespace Lax560851.StructuralCombinators.Generated
end Lax560851.StructuralCombinators.Generated

namespace Lax560851.StructuralCombinators.Lawful
end Lax560851.StructuralCombinators.Lawful

namespace Lax560851.StructuralCombinators.Raw
end Lax560851.StructuralCombinators.Raw

namespace Lax560851.StructuralCombinators.SizeLaws
end Lax560851.StructuralCombinators.SizeLaws

namespace Lax560851.StructuralCombinators.listFromRaw
end Lax560851.StructuralCombinators.listFromRaw

namespace Lax560851.StructuralCombinators.listToRaw
end Lax560851.StructuralCombinators.listToRaw

namespace Lax560851.StructuralCombinators.nat
end Lax560851.StructuralCombinators.nat

namespace Lax560851.StructuralCombinators.prod
end Lax560851.StructuralCombinators.prod

namespace Lax560851.StructuralCombinators.Raw.constructorCharsCode
end Lax560851.StructuralCombinators.Raw.constructorCharsCode

namespace Lax560851.StructuralCombinators.Raw.fields
end Lax560851.StructuralCombinators.Raw.fields
end

-- Lax263307.IndependentSetEncoding
section
namespace Lax263307.IndependentSetEncoding
end Lax263307.IndependentSetEncoding
end

-- Lax263307.MaxWeightIndependentSet
section
namespace Lax263307

open GraphClasses WeightedIndependentSet

open Lax213208.OptimizationProblem

namespace MaxWeightIndependentSet

/-- Weighted graphs whose underlying graph belongs to the given class. -/
def instancesOn (C : GraphClass) : Set Instance :=
  {x | x.graph ∈ C x.order}

end MaxWeightIndependentSet

end Lax263307
end
