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
namespace Lax678846.FiniteStructures.Isomorphism
end Lax678846.FiniteStructures.Isomorphism

namespace Lax678846.FiniteStructures

abbrev Vocabulary := Lax979537.OrderedStructures.Vocabulary

abbrev Symbol := Lax979537.OrderedStructures.Symbol

abbrev Structure := Lax979537.OrderedStructures.OrderedStructure

abbrev Interpretation (σ : Vocabulary) (n : Nat) :=
  (r : Symbol σ) → (Fin (σ.get r) → Fin n) → Bool

end Lax678846.FiniteStructures
end

-- Lax678846.ExistentialSecondOrder
section
namespace Lax678846.ExistentialSecondOrder.Sentence
end Lax678846.ExistentialSecondOrder.Sentence

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

end Lax678846.ExistentialSecondOrder
end
