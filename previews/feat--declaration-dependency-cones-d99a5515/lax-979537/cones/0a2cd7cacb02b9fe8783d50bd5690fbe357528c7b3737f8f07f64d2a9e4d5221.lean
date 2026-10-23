-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Set.Lattice

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

-- Lax979537.FixedPointSyntax
section
namespace Lax979537.FixedPointSyntax

open Lax979537.OrderedStructures

inductive RawFormula (σ : Vocabulary) : Nat → List Nat → Type
  | truth {m ρ} : RawFormula σ m ρ
  | equal {m ρ} (x y : Fin m) : RawFormula σ m ρ
  | less {m ρ} (x y : Fin m) : RawFormula σ m ρ
  | relation {m ρ} (r : Symbol σ) (args : Fin (σ.get r) → Fin m) :
      RawFormula σ m ρ
  | variable {m ρ} (r : Fin ρ.length) (args : Fin (ρ.get r) → Fin m) :
      RawFormula σ m ρ
  | neg {m ρ} (φ : RawFormula σ m ρ) : RawFormula σ m ρ
  | conj {m ρ} (φ ψ : RawFormula σ m ρ) : RawFormula σ m ρ
  | exists' {m ρ} (φ : RawFormula σ (m + 1) ρ) : RawFormula σ m ρ
  | lfp {m ρ} (k : Nat) (body : RawFormula σ (k + m) (k :: ρ))
      (args : Fin k → Fin m) : RawFormula σ m ρ

/-- Every occurrence of `r` has the required polarity. `true` means positive. -/
def RawFormula.positiveAt {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (r : Fin ρ.length) (polarity : Bool) : Prop :=
  match φ with
  | .truth | .equal _ _ | .less _ _ | .relation _ _ => True
  | .variable s _ => s = r → polarity = true
  | .neg ψ => ψ.positiveAt r (!polarity)
  | .conj ψ χ => ψ.positiveAt r polarity ∧ χ.positiveAt r polarity
  | .exists' ψ => ψ.positiveAt r polarity
  | .lfp _ body _ => body.positiveAt r.succ polarity

/-- Every fixed-point binder has a positive defining body. -/
def RawFormula.Admissible {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) : Prop :=
  match φ with
  | .truth | .equal _ _ | .less _ _ | .relation _ _ | .variable _ _ => True
  | .neg ψ | .exists' ψ => ψ.Admissible
  | .conj ψ χ => ψ.Admissible ∧ χ.Admissible
  | .lfp _ body _ => body.Admissible ∧ body.positiveAt 0 true

abbrev Formula (σ : Vocabulary) (m : Nat) :=
  {φ : RawFormula σ m [] // φ.Admissible}

end Lax979537.FixedPointSyntax
end

-- Lax979537.LeastFixedPoints
section
namespace Lax979537.LeastFixedPoints.stage
end Lax979537.LeastFixedPoints.stage

namespace Lax979537.LeastFixedPoints

def leastFixedPoint {α : Type} (F : Set α → Set α) : Set α :=
  sInf {R | F R ⊆ R}

end Lax979537.LeastFixedPoints
end

-- Lax979537.FixedPointSemantics
section
namespace Lax979537.FixedPointSemantics

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax

open Lax979537.LeastFixedPoints

abbrev RelationEnv (n : Nat) (ρ : List Nat) :=
  (r : Fin ρ.length) → Set (Fin (ρ.get r) → Fin n)

def extend {n k : Nat} {ρ : List Nat} (R : Set (Fin k → Fin n))
    (η : RelationEnv n ρ) : RelationEnv n (k :: ρ) :=
  Fin.cons R η

def eval {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) : Prop :=
  match φ with
  | .truth => True
  | .equal x y => v x = v y
  | .less x y => v x < v y
  | .relation r args => A.relation r (v ∘ args) = true
  | .variable r args => η r (v ∘ args)
  | .neg ψ => ¬ eval ψ A v η
  | .conj ψ χ => eval ψ A v η ∧ eval χ A v η
  | .exists' ψ => ∃ a, eval ψ A (Fin.cons a v) η
  | .lfp _ body args =>
      leastFixedPoint (fun R => {a | eval body A (Fin.append a v) (extend R η)})
        (v ∘ args)

def Satisfies {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k)
    (φ : Formula σ k) : Prop :=
  eval φ.val A.structureValue A.tuple (fun r => Fin.elim0 r)

def Definable {σ : Vocabulary} {k : Nat} (Q : Query σ k) : Prop :=
  ∃ φ : Formula σ k, ∀ A, Q A ↔ Satisfies A φ

end Lax979537.FixedPointSemantics
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

def InP {σ : Vocabulary} {k : Nat} (Q : Query σ k) : Prop :=
  ∃ f : List Bool → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime id (fun b => [b]) f) ∧
    ∀ w, f w = true ↔ language Q w

end Lax979537.PolynomialTime
end

-- Lax979537.FixedPointEvaluation
section
namespace Lax979537.FixedPointEvaluation
end Lax979537.FixedPointEvaluation
end

-- Lax979537.ImmermanVardi
section
namespace Lax979537.ImmermanVardi

open Lax979537.OrderedStructures Lax979537.FixedPointSemantics

open Lax979537.PolynomialTime

axiom capturesPtime {σ : Vocabulary} {k : Nat} (Q : Query σ k) :
    Definable Q ↔ InP Q

end Lax979537.ImmermanVardi
end
