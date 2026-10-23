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

abbrev Query (σ : Vocabulary) (k : Nat) := PointedStructure σ k → Prop

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

-- Lax979537.PolynomialTime
section
namespace Lax979537.PolynomialTime

open Lax979537.OrderedStructures Lax979537.StructureEncoding

def language {σ : Vocabulary} {k : Nat} (Q : Query σ k) (w : List Bool) : Prop :=
  ∃ A : PointedStructure σ k, encode A = w ∧ Q A

end Lax979537.PolynomialTime
end
