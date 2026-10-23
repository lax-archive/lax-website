-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Real.Basic

-- Lax323828.Graphs
section
namespace Lax323828.Graphs

/-- A simple graph represented by a symmetric Boolean adjacency matrix with zero diagonal. -/
structure Graph (n : ℕ) where
  /-- Whether the two labeled vertices are adjacent. -/
  adjacent : Fin n → Fin n → Bool
  /-- No vertex is adjacent to itself. -/
  loopless : ∀ v, adjacent v v = false
  /-- Adjacency is unchanged when the endpoints are exchanged. -/
  symmetric : ∀ u v, adjacent u v = adjacent v u

/-- Read the Boolean matrix as a mathematical simple graph. -/
def Graph.simpleGraph {n : ℕ} (G : Graph n) : SimpleGraph (Fin n) where
  Adj u v := G.adjacent u v = true
  symm := ⟨fun u v h ↦ (G.symmetric u v).symm.trans h⟩
  loopless := ⟨fun v h ↦ Bool.noConfusion ((G.loopless v).symm.trans h)⟩

/-- The vertex count in unary, a separator, and the adjacency matrix in row order. -/
def Graph.encode {n : ℕ} (G : Graph n) : List Bool :=
  List.replicate n true ++ [false] ++
    (List.finRange n).flatMap (fun u ↦ (List.finRange n).map (G.adjacent u))

/-- The maximum number of pairwise adjacent vertices. -/
noncomputable def Graph.cliqueNumber {n : ℕ} (G : Graph n) : ℕ :=
  G.simpleGraph.cliqueNum

end Lax323828.Graphs
end

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax323828.Approximation
section
namespace Lax323828.Approximation
end Lax323828.Approximation
end

-- Lax323828.FiniteProbability
section
namespace Lax323828.FiniteProbability

open scoped Classical

open scoped BigOperators

/-- The proportion of points in the finite sample space satisfying the event `P`. -/
noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax323828.FiniteProbability
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

-- Lax323828.RandomizedApproximation
section
namespace Lax323828.RandomizedApproximation

open Graphs FiniteProbability Lax434930.PolynomialTime

def Good {n : ℕ} (ε : ℝ) (G : Graph n) (a : ℕ) : Prop :=
  a ≤ G.cliqueNumber ∧
    (G.cliqueNumber : ℝ) ≤ Real.rpow (n : ℝ) (1 - ε) * (a : ℝ)

def Approximable (ε : ℝ) : Prop :=
  ∃ (coins : Polynomial ℕ) (estimate : Word → ℕ),
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
    ∀ (n : ℕ), 0 < n → ∀ G : Graph n,
      (2 / 3 : ℝ) ≤ probability (fun r : Fin (coins.eval G.encode.length) → Bool ↦
        Good ε G (estimate (Lax434930.Certificates.pair G.encode (List.ofFn r))))

end Lax323828.RandomizedApproximation
end
