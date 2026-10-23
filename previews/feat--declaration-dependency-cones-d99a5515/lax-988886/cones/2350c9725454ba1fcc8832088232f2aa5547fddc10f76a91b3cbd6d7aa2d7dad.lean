-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

-- Lax751879.OrderedStructures
section
namespace Lax751879.OrderedStructures.OrderedStructure
end Lax751879.OrderedStructures.OrderedStructure

namespace Lax751879.OrderedStructures.PointedStructure
end Lax751879.OrderedStructures.PointedStructure

namespace Lax751879.OrderedStructures

abbrev Vocabulary := List Nat

/-- Relation symbols are numbered in the order of the vocabulary. -/
abbrev Symbol (σ : Vocabulary) := Fin σ.length

end Lax751879.OrderedStructures
end

-- Lax751879.StructureEncoding
section
namespace Lax751879.StructureEncoding
end Lax751879.StructureEncoding

namespace Lax751879.StructureEncoding.tuples
end Lax751879.StructureEncoding.tuples
end

-- Lax988886.FiniteStructures
section
namespace Lax988886.FiniteStructures.Isomorphism
end Lax988886.FiniteStructures.Isomorphism

namespace Lax988886.FiniteStructures

abbrev Vocabulary := Lax751879.OrderedStructures.Vocabulary

abbrev Symbol := Lax751879.OrderedStructures.Symbol

end Lax988886.FiniteStructures
end

-- Lax988886.ExistentialSecondOrder
section
namespace Lax988886.ExistentialSecondOrder.Sentence
end Lax988886.ExistentialSecondOrder.Sentence

namespace Lax988886.ExistentialSecondOrder.FirstOrder.eval
end Lax988886.ExistentialSecondOrder.FirstOrder.eval

namespace Lax988886.ExistentialSecondOrder

open Lax988886.FiniteStructures

inductive FirstOrder (σ τ : Vocabulary) : Nat → Type
  | truth {m} : FirstOrder σ τ m
  | equal {m} (x y : Fin m) : FirstOrder σ τ m
  | relation {m} (r : Symbol σ) (args : Fin (σ.get r) → Fin m) : FirstOrder σ τ m
  | variable {m} (r : Symbol τ) (args : Fin (τ.get r) → Fin m) : FirstOrder σ τ m
  | neg {m} (φ : FirstOrder σ τ m) : FirstOrder σ τ m
  | conj {m} (φ ψ : FirstOrder σ τ m) : FirstOrder σ τ m
  | exists' {m} (φ : FirstOrder σ τ (m + 1)) : FirstOrder σ τ m

end Lax988886.ExistentialSecondOrder
end
