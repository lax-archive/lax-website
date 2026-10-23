-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

-- Lax979537.OrderedStructures
section
namespace Lax979537.OrderedStructures.OrderedStructure
end Lax979537.OrderedStructures.OrderedStructure

namespace Lax979537.OrderedStructures.PointedStructure
end Lax979537.OrderedStructures.PointedStructure

namespace Lax979537.OrderedStructures

abbrev Vocabulary := List Nat

/-- Relation symbols are numbered in the order of the vocabulary. -/
abbrev Symbol (σ : Vocabulary) := Fin σ.length

end Lax979537.OrderedStructures
end

-- Lax979537.StructureEncoding
section
namespace Lax979537.StructureEncoding
end Lax979537.StructureEncoding

namespace Lax979537.StructureEncoding.tuples
end Lax979537.StructureEncoding.tuples
end

-- Lax678846.FiniteStructures
section
namespace Lax678846.FiniteStructures.Isomorphism
end Lax678846.FiniteStructures.Isomorphism

namespace Lax678846.FiniteStructures

abbrev Vocabulary := Lax979537.OrderedStructures.Vocabulary

abbrev Symbol := Lax979537.OrderedStructures.Symbol

end Lax678846.FiniteStructures
end

-- Lax678846.ExistentialSecondOrder
section
namespace Lax678846.ExistentialSecondOrder.FirstOrder.eval
end Lax678846.ExistentialSecondOrder.FirstOrder.eval

namespace Lax678846.ExistentialSecondOrder

open Lax678846.FiniteStructures

inductive FirstOrder (σ τ : Vocabulary) : Nat → Type
  | truth {m} : FirstOrder σ τ m
  | equal {m} (x y : Fin m) : FirstOrder σ τ m
  | relation {m} (r : Symbol σ) (args : Fin (σ.get r) → Fin m) : FirstOrder σ τ m
  | variable {m} (r : Symbol τ) (args : Fin (τ.get r) → Fin m) : FirstOrder σ τ m
  | neg {m} (φ : FirstOrder σ τ m) : FirstOrder σ τ m
  | conj {m} (φ ψ : FirstOrder σ τ m) : FirstOrder σ τ m
  | exists' {m} (φ : FirstOrder σ τ (m + 1)) : FirstOrder σ τ m

structure Sentence (σ : Vocabulary) where
  witnesses : Vocabulary
  matrix : FirstOrder σ witnesses 0

end Lax678846.ExistentialSecondOrder
end
