-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Set.Lattice

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

-- Lax751879.FixedPointSyntax
section
namespace Lax751879.FixedPointSyntax.RawFormula.Admissible
end Lax751879.FixedPointSyntax.RawFormula.Admissible

namespace Lax751879.FixedPointSyntax.RawFormula.positiveAt
end Lax751879.FixedPointSyntax.RawFormula.positiveAt

namespace Lax751879.FixedPointSyntax

open Lax751879.OrderedStructures

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

end Lax751879.FixedPointSyntax
end

-- Lax751879.LeastFixedPoints
section
namespace Lax751879.LeastFixedPoints.stage
end Lax751879.LeastFixedPoints.stage

namespace Lax751879.LeastFixedPoints

def leastFixedPoint {α : Type} (F : Set α → Set α) : Set α :=
  sInf {R | F R ⊆ R}

end Lax751879.LeastFixedPoints
end

-- Lax751879.FixedPointSemantics
section
namespace Lax751879.FixedPointSemantics

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax

open Lax751879.LeastFixedPoints

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

end Lax751879.FixedPointSemantics
end
