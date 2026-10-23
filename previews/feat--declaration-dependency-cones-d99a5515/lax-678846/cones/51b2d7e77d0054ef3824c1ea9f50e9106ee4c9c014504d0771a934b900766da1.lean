-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Computability.TuringMachine.Computable
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

end Lax979537.OrderedStructures
end

-- Lax979537.StructureEncoding
section
namespace Lax979537.StructureEncoding

open Lax979537.OrderedStructures

/-- All tuples, with the first coordinate varying slowest. -/
def tuples (n : Nat) : (k : Nat) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k + 1 => (List.finRange n).flatMap fun a =>
      (tuples n k).map (Fin.cons a)

def unary (n : Nat) : List Bool := List.replicate n true ++ [false]

def encode {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) : List Bool :=
  unary A.structureValue.size ++
    (List.finRange σ.length).flatMap (fun r =>
      (tuples A.structureValue.size (σ.get r)).map (A.structureValue.relation r)) ++
    (List.finRange k).flatMap (fun i => unary (A.tuple i).val)

end Lax979537.StructureEncoding
end

-- Lax678846.FiniteStructures
section
namespace Lax678846.FiniteStructures.Isomorphism
end Lax678846.FiniteStructures.Isomorphism

namespace Lax678846.FiniteStructures

abbrev Vocabulary := Lax979537.OrderedStructures.Vocabulary

abbrev Structure := Lax979537.OrderedStructures.OrderedStructure

abbrev Property (σ : Vocabulary) := Structure σ → Prop

def encode {σ : Vocabulary} (A : Structure σ) : List Bool :=
  Lax979537.StructureEncoding.encode ⟨A, Fin.elim0⟩

def language {σ : Vocabulary} (Q : Property σ) (w : List Bool) : Prop :=
  ∃ A : Structure σ, encode A = w ∧ Q A

end Lax678846.FiniteStructures
end

-- Lax678846.NondeterministicPolynomialTime
section
namespace Lax678846.NondeterministicPolynomialTime

open Lax678846.FiniteStructures

def encodePair (p : List Bool × List Bool) : List Bool :=
  p.1.flatMap (fun b => [true, b]) ++ false :: p.2

def LanguageInNP (L : List Bool → Prop) : Prop :=
  ∃ (V : List Bool × List Bool → Bool) (p : Polynomial Nat),
    Nonempty (Turing.TM2ComputableInPolyTime encodePair (fun b => [b]) V) ∧
    ∀ w, L w ↔ ∃ c : List Bool, c.length ≤ p.eval w.length ∧ V (w, c) = true

def InNP {σ : Vocabulary} (Q : Property σ) : Prop :=
  LanguageInNP (language Q)

end Lax678846.NondeterministicPolynomialTime
end
