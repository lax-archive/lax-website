-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

-- Lax979537.OrderedStructures
section
namespace Lax979537.OrderedStructures

abbrev Vocabulary := List Nat

/-- Relation symbols are numbered in the order of the vocabulary. -/
abbrev Symbol (σ : Vocabulary) := Fin σ.length

structure OrderedStructure (σ : Vocabulary) where
  size : Nat
  relation : (r : Symbol σ) → (Fin (σ.get r) → Fin size) → Bool

structure PointedStructure (σ : Vocabulary) (k : Nat) where
  structureValue : OrderedStructure σ
  tuple : Fin k → Fin structureValue.size

abbrev Query (σ : Vocabulary) (k : Nat) := PointedStructure σ k → Prop

end Lax979537.OrderedStructures
end
