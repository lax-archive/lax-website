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
namespace Lax988886.FiniteStructures.Isomorphism
end Lax988886.FiniteStructures.Isomorphism

namespace Lax988886.FiniteStructures

abbrev Vocabulary := Lax751879.OrderedStructures.Vocabulary

abbrev Symbol := Lax751879.OrderedStructures.Symbol

abbrev Structure := Lax751879.OrderedStructures.OrderedStructure

abbrev Interpretation (σ : Vocabulary) (n : Nat) :=
  (r : Symbol σ) → (Fin (σ.get r) → Fin n) → Bool

end Lax988886.FiniteStructures
end

-- Lax988886.ExistentialSecondOrder
section
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

def FirstOrder.eval {σ τ : Vocabulary} {m : Nat} (φ : FirstOrder σ τ m)
    (A : Structure σ) (R : Interpretation τ A.size) (v : Fin m → Fin A.size) : Prop :=
  match φ with
  | .truth => True
  | .equal x y => v x = v y
  | .relation r args => A.relation r (v ∘ args) = true
  | .variable r args => R r (v ∘ args) = true
  | .neg ψ => ¬ ψ.eval A R v
  | .conj ψ χ => ψ.eval A R v ∧ χ.eval A R v
  | .exists' ψ => ∃ a : Fin A.size, ψ.eval A R (Fin.cons a v)

structure Sentence (σ : Vocabulary) where
  witnesses : Vocabulary
  matrix : FirstOrder σ witnesses 0

def Satisfies {σ : Vocabulary} (A : Structure σ) (φ : Sentence σ) : Prop :=
  ∃ R : Interpretation φ.witnesses A.size, φ.matrix.eval A R Fin.elim0

end Lax988886.ExistentialSecondOrder
end
