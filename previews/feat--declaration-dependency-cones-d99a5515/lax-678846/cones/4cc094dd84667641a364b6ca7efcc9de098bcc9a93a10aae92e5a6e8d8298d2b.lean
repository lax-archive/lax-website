-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

-- Lax979537.OrderedStructures
section
namespace Lax979537.OrderedStructures.PointedStructure
end Lax979537.OrderedStructures.PointedStructure

namespace Lax979537.OrderedStructures

abbrev Vocabulary := List Nat

/-- Relation symbols are numbered in the order of the vocabulary. -/
abbrev Symbol (σ : Vocabulary) := Fin σ.length

structure OrderedStructure (σ : Vocabulary) where
  size : Nat
  relation : (r : Symbol σ) → (Fin (σ.get r) → Fin size) → Bool

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
namespace Lax678846.FiniteStructures

abbrev Vocabulary := Lax979537.OrderedStructures.Vocabulary

abbrev Symbol := Lax979537.OrderedStructures.Symbol

abbrev Structure := Lax979537.OrderedStructures.OrderedStructure

structure Isomorphism {σ : Vocabulary} (A B : Structure σ) where
  equivalence : Fin A.size ≃ Fin B.size
  preserves : ∀ (r : Symbol σ) (a : Fin (σ.get r) → Fin A.size),
    B.relation r (equivalence ∘ a) = A.relation r a

end Lax678846.FiniteStructures
end
