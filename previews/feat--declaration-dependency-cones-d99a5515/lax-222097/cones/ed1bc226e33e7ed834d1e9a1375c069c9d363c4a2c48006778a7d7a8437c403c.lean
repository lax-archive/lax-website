-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}

end Lax434930.PolynomialTime
end

-- Lax222097.GraphEncoding
section
namespace Lax222097.GraphEncoding

open scoped Classical

open List Turing Lax434930.PolynomialTime

/-- An input graph together with the requested solution-size threshold. -/
structure Instance where
  /-- The number of vertices. -/
  order : ℕ
  /-- A simple graph on vertices numbered from zero to `order - 1`. -/
  graph : SimpleGraph (Fin order)
  /-- The requested lower bound on the size of a solution. -/
  threshold : ℕ

/-- Encode a natural number as that many one-bits followed by a zero-bit. -/
def unary (n : ℕ) : Word := replicate n true ++ [false]

/-- Write the vertex count, the adjacency matrix row by row, and the threshold. -/
noncomputable def encode (I : Instance) : Word :=
  unary I.order ++
    (finRange I.order).flatMap (fun u =>
      (finRange I.order).map (fun v => decide (I.graph.Adj u v))) ++
    unary I.threshold

end Lax222097.GraphEncoding
end

-- Lax222097.MaxCut
section
namespace Lax222097.MaxCut
end Lax222097.MaxCut
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair

namespace Lax434930.Certificates

open PolynomialTime

/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y

end Lax434930.Certificates
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime

open PolynomialTime Certificates

/-- Languages with polynomially bounded, polynomial-time verifiable certificates. -/
def NP : Set Language :=
  {A | ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V}

end Lax434930.NondeterministicPolynomialTime
end

-- Lax222097.GraphProblems
section
namespace Lax222097.GraphProblems

open GraphEncoding MaxCut Turing

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

abbrev GraphClass := ∀ {n : ℕ}, SimpleGraph (Fin n) → Prop

abbrev DecisionProblem := Instance → Prop

def IndependentSet (I : Instance) : Prop := I.threshold ≤ I.graph.indepNum

def NPHardOn (problem : DecisionProblem) (graphs : GraphClass) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → Instance,
      Nonempty (TM2ComputableInPolyTime id encode f) ∧
      ∀ x, graphs (f x).graph ∧ (x ∈ A ↔ problem (f x))

end Lax222097.GraphProblems
end

-- Lax222097.InducedMinors
section
namespace Lax222097.InducedMinors

open SimpleGraph

structure Model {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) where
  branch : W → Set V
  connected : ∀ v, Connected (G.induce (branch v))
  disjoint : ∀ u v, u ≠ v → Disjoint (branch u) (branch v)
  adjacent : ∀ u v, u ≠ v →
    (H.Adj u v ↔ ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y)

def IsInducedMinor {W V : Type*} (H : SimpleGraph W)
    (G : SimpleGraph V) : Prop :=
  Nonempty (Model H G)

end Lax222097.InducedMinors
end

-- Lax222097.Grid
section
namespace Lax222097.Grid

open SimpleGraph InducedMinors

def squareGrid (k : ℕ) : SimpleGraph (Fin k × Fin k) :=
  (pathGraph k).boxProd (pathGraph k)

def ExcludesInducedGrid (k : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ IsInducedMinor (squareGrid k) G

end Lax222097.Grid
end

-- Lax222097.IndependentSetHardness
section
namespace Lax222097.IndependentSetHardness

open GraphProblems Grid

axiom independentSet_inducedGrid_hardness :
  NPHardOn IndependentSet (ExcludesInducedGrid 5)

end Lax222097.IndependentSetHardness
end
