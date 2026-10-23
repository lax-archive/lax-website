-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

-- Lax751879.OrderedStructures
section
namespace Lax751879.OrderedStructures

abbrev Vocabulary := List Nat

/-- Relation symbols are numbered in the order of the vocabulary. -/
abbrev Symbol (σ : Vocabulary) := Fin σ.length

structure OrderedStructure (σ : Vocabulary) where
  size : Nat
  relation : (r : Symbol σ) → (Fin (σ.get r) → Fin size) → Bool

structure PointedStructure (σ : Vocabulary) (k : Nat) where
  structureValue : OrderedStructure σ
  tuple : Fin k → Fin structureValue.size

end Lax751879.OrderedStructures
end

-- Lax751879.StructureEncoding
section
namespace Lax751879.StructureEncoding

open Lax751879.OrderedStructures

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

end Lax751879.StructureEncoding
end

-- Lax988886.FiniteStructures
section
namespace Lax988886.FiniteStructures

abbrev Vocabulary := Lax751879.OrderedStructures.Vocabulary

abbrev Symbol := Lax751879.OrderedStructures.Symbol

abbrev Structure := Lax751879.OrderedStructures.OrderedStructure

abbrev Interpretation (σ : Vocabulary) (n : Nat) :=
  (r : Symbol σ) → (Fin (σ.get r) → Fin n) → Bool

abbrev Property (σ : Vocabulary) := Structure σ → Prop

structure Isomorphism {σ : Vocabulary} (A B : Structure σ) where
  equivalence : Fin A.size ≃ Fin B.size
  preserves : ∀ (r : Symbol σ) (a : Fin (σ.get r) → Fin A.size),
    B.relation r (equivalence ∘ a) = A.relation r a

def IsomorphismInvariant {σ : Vocabulary} (Q : Property σ) : Prop :=
  ∀ A B : Structure σ, Nonempty (Isomorphism A B) → (Q A ↔ Q B)

def encode {σ : Vocabulary} (A : Structure σ) : List Bool :=
  Lax751879.StructureEncoding.encode ⟨A, Fin.elim0⟩

def language {σ : Vocabulary} (Q : Property σ) (w : List Bool) : Prop :=
  ∃ A : Structure σ, encode A = w ∧ Q A

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

def Definable {σ : Vocabulary} (Q : Property σ) : Prop :=
  ∃ φ : Sentence σ, ∀ A : Structure σ, Q A ↔ Satisfies A φ

end Lax988886.ExistentialSecondOrder
end

-- Lax988886.NondeterministicPolynomialTime
section
namespace Lax988886.NondeterministicPolynomialTime

open Lax988886.FiniteStructures

def encodePair (p : List Bool × List Bool) : List Bool :=
  p.1.flatMap (fun b => [true, b]) ++ false :: p.2

def LanguageInNP (L : List Bool → Prop) : Prop :=
  ∃ (V : List Bool × List Bool → Bool) (p : Polynomial Nat),
    Nonempty (Turing.TM2ComputableInPolyTime encodePair (fun b => [b]) V) ∧
    ∀ w, L w ↔ ∃ c : List Bool, c.length ≤ p.eval w.length ∧ V (w, c) = true

def InNP {σ : Vocabulary} (Q : Property σ) : Prop :=
  LanguageInNP (language Q)

end Lax988886.NondeterministicPolynomialTime
end

-- Lax988886.Fagin
section
namespace Lax988886.Fagin

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder

open Lax988886.NondeterministicPolynomialTime

axiom capturesNP {σ : Vocabulary} (Q : Property σ)
    (hQ : IsomorphismInvariant Q) : Definable Q ↔ InNP Q

end Lax988886.Fagin
end
