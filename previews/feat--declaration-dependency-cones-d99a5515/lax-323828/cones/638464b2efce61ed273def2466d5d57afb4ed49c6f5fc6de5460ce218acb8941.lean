-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange

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

open Graphs

open Lax434930.PolynomialTime

def Approximable (ε : ℝ) : Prop :=
  ∃ estimate : Word → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
    ∀ (n : ℕ), 0 < n → ∀ G : Graph n,
      estimate G.encode ≤ G.cliqueNumber ∧
      (G.cliqueNumber : ℝ) ≤ Real.rpow (n : ℝ) (1 - ε) * (estimate G.encode : ℝ)

end Lax323828.Approximation
end
