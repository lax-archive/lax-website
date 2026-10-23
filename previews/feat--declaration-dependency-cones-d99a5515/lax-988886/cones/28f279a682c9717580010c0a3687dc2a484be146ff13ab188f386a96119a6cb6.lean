-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

-- Lax751879.OrderedStructures
section
namespace Lax751879.OrderedStructures.PointedStructure
end Lax751879.OrderedStructures.PointedStructure

namespace Lax751879.OrderedStructures

abbrev Vocabulary := List Nat

/-- Relation symbols are numbered in the order of the vocabulary. -/
abbrev Symbol (σ : Vocabulary) := Fin σ.length

structure OrderedStructure (σ : Vocabulary) where
  size : Nat
  relation : (r : Symbol σ) → (Fin (σ.get r) → Fin size) → Bool

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
namespace Lax988886.FiniteStructures

abbrev Vocabulary := Lax751879.OrderedStructures.Vocabulary

abbrev Symbol := Lax751879.OrderedStructures.Symbol

abbrev Structure := Lax751879.OrderedStructures.OrderedStructure

abbrev Property (σ : Vocabulary) := Structure σ → Prop

structure Isomorphism {σ : Vocabulary} (A B : Structure σ) where
  equivalence : Fin A.size ≃ Fin B.size
  preserves : ∀ (r : Symbol σ) (a : Fin (σ.get r) → Fin A.size),
    B.relation r (equivalence ∘ a) = A.relation r a

def IsomorphismInvariant {σ : Vocabulary} (Q : Property σ) : Prop :=
  ∀ A B : Structure σ, Nonempty (Isomorphism A B) → (Q A ↔ Q B)

end Lax988886.FiniteStructures
end
