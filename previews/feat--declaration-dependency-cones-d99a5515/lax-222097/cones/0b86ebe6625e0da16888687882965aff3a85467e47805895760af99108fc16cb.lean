-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
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

open scoped Classical

open Finset

/-- All edges, each listed once with its smaller endpoint first. -/
noncomputable def edges {n : ℕ} (F : SimpleGraph (Fin n)) :
    Finset (Fin n × Fin n) :=
  univ.filter fun e => e.1 < e.2 ∧ F.Adj e.1 e.2

/-- The number of edges crossing between `S` and its complement. -/
noncomputable def cutSize {n : ℕ} (F : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  ((edges F).filter fun e =>
    (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)).card

/-- The largest cut size over all subsets of vertices. -/
noncomputable def maxCut {n : ℕ} (F : SimpleGraph (Fin n)) : ℕ :=
  (univ : Finset (Fin n)).powerset.sup (cutSize F)

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

abbrev DecisionProblem := Instance → Prop

def MaxCut (I : Instance) : Prop := I.threshold ≤ maxCut I.graph

def NPHard (problem : DecisionProblem) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → Instance,
      Nonempty (TM2ComputableInPolyTime id encode f) ∧
      ∀ x, x ∈ A ↔ problem (f x)

end Lax222097.GraphProblems
end

-- Lax222097.MaxCutHardness
section
namespace Lax222097.MaxCutHardness

open GraphProblems

axiom maxCut_hardness : NPHard MaxCut

end Lax222097.MaxCutHardness
end
