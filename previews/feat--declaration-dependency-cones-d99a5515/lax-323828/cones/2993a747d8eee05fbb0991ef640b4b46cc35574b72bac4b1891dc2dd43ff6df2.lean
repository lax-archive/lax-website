-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.FreshBitSampling
section
namespace Lax323828.FreshBitSampling

open FiniteProbability

def modulo {N r B : ℕ} (hr : 0 < r) (z : Fin N → Fin B) : Fin N → Fin r :=
  fun i ↦ ⟨(z i).val % r, Nat.mod_lt _ hr⟩

def bitsPerDraw (N r : ℕ) : ℕ := Nat.clog 2 (12 * N * r)

def binaryEquiv (b : ℕ) : (Fin b → Bool) ≃ Fin (2 ^ b) :=
  (Equiv.piCongrRight (fun _ ↦ finTwoEquiv.symm)).trans finFunctionFinEquiv

def sample {N r : ℕ} (hr : 0 < r)
    (z : Fin N → Fin (bitsPerDraw N r) → Bool) : Fin N → Fin r :=
  modulo hr (fun i ↦ binaryEquiv (bitsPerDraw N r) (z i))

def coinEquiv (N b : ℕ) : (Fin (N * b) → Bool) ≃ (Fin N → Fin b → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def sampleFlat {N r : ℕ} (hr : 0 < r)
    (coins : Fin (N * bitsPerDraw N r) → Bool) : Fin N → Fin r :=
  sample hr (coinEquiv N (bitsPerDraw N r) coins)

end Lax323828.FreshBitSampling
end

-- Lax323828.BernoulliSampling
section
namespace Lax323828.BernoulliSampling
end Lax323828.BernoulliSampling
end

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

/-- The vertex count in unary, a separator, and the adjacency matrix in row order. -/
def Graph.encode {n : ℕ} (G : Graph n) : List Bool :=
  List.replicate n true ++ [false] ++
    (List.finRange n).flatMap (fun u ↦ (List.finRange n).map (G.adjacent u))

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

-- Lax323828.LocalTests
section
namespace Lax323828.LocalTests

open scoped Classical

/-- A partial proof; `none` means that the position is not queried. -/
abbrev View (m : ℕ) := Fin m → Option Bool

/-- The two partial views agree at all positions where both specify an answer. -/
def Compatible {m : ℕ} (a b : View m) : Prop :=
  ∀ i x y, a i = some x → b i = some y → x = y

/-- For each random choice, the collection of local views that make the verifier accept. -/
structure System (r m : ℕ) where
  /-- The acceptable partial answer patterns for this random choice. -/
  accepting : Fin r → Finset (View m)

end Lax323828.LocalTests
end

-- Lax323828.ConsistencyGraph
section
namespace Lax323828.ConsistencyGraph

open LocalTests

abbrev Vertex {r m : ℕ} (C : System r m) :=
  (seed : Fin r) × {a // a ∈ C.accepting seed}

def graph {r m : ℕ} (C : System r m) : SimpleGraph (Vertex C) where
  Adj u v := u.1 ≠ v.1 ∧ Compatible u.2.1 v.2.1
  symm := ⟨fun _ _ h ↦ ⟨Ne.symm h.1,
    fun i x y hx hy ↦ (h.2 i y x hy hx).symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

end Lax323828.ConsistencyGraph
end

-- Lax323828.CliqueCorrespondence
section
namespace Lax323828.CliqueCorrespondence
end Lax323828.CliqueCorrespondence
end

-- Lax323828.GraphEncoding
section
namespace Lax323828.GraphEncoding

open Graphs

/-- Transfer adjacency along the vertex numbering `e` to obtain a Boolean matrix. -/
def numbered {α : Type} {n : ℕ} (G : SimpleGraph α) [DecidableRel G.Adj]
    (e : Fin n ≃ α) : Graph n where
  adjacent u v := decide (G.Adj (e u) (e v))
  loopless v := decide_eq_false (G.loopless.irrefl (e v))
  symmetric u v := decide_eq_decide.mpr (G.adj_comm (e u) (e v))

end Lax323828.GraphEncoding
end

-- Lax323828.EncodedReduction
section
namespace Lax323828.EncodedReduction

open scoped Classical

open LocalTests ConsistencyGraph Lax434930.PolynomialTime

/-- The consistency graph with consecutively numbered vertices, in the approximation algorithm’s input format. -/
noncomputable def output {r m : ℕ} (C : System r m) :
    Graphs.Graph (Fintype.card (Vertex C)) :=
  GraphEncoding.numbered (graph C) (Fintype.equivFin (Vertex C)).symm

end Lax323828.EncodedReduction
end

-- Lax323828.TestSampling
section
namespace Lax323828.TestSampling

open LocalTests FiniteProbability ConsistencyGraph

def sampled {r m N : ℕ} (C : System r m) (z : Fin N → Fin r) : System N m :=
  ⟨fun i ↦ C.accepting (z i)⟩

end Lax323828.TestSampling
end

-- Lax323828.TestRepetition
section
namespace Lax323828.TestRepetition

open scoped Classical

open LocalTests TestSampling FiniteProbability

/-- Every pair of local views gives the same answer wherever both are defined. -/
def Coherent {m k : ℕ} (a : Fin k → View m) : Prop :=
  ∀ i j, Compatible (a i) (a j)

/-- Combine the views into one partial assignment, using the first available answer at each coordinate. -/
def merge {m : ℕ} : {k : ℕ} → (Fin k → View m) → View m
  | 0, _ => fun _ ↦ none
  | k + 1, a => fun i ↦ (a 0 i).or (merge (fun j : Fin k ↦ a j.succ) i)

/-- Number the `r^k` sequences of `k` random choices using their base-`r` digits. -/
def seedEquiv (r k : ℕ) : (Fin k → Fin r) ≃ Fin (r ^ k) :=
  finFunctionFinEquiv

/-- Keep every coherent combination of accepting views from the `k` runs, and merge each combination. -/
noncomputable def repeated {r m : ℕ} (C : System r m) (k : ℕ) : System (r ^ k) m :=
  ⟨fun z ↦ ((Fintype.piFinset (fun i : Fin k ↦ C.accepting ((seedEquiv r k).symm z i))).filter
    Coherent).image merge⟩

end Lax323828.TestRepetition
end

-- Lax323828.SamplingParameters
section
namespace Lax323828.SamplingParameters

def sampleCount (t k m : ℕ) : ℕ := (m + 2) * 2 ^ (t * k)

def threshold (m : ℕ) : ℕ := 4 * (m + 2)

end Lax323828.SamplingParameters
end

-- Lax323828.RandomizedReduction
section
namespace Lax323828.RandomizedReduction

open LocalTests ConsistencyGraph TestSampling TestRepetition SamplingParameters FiniteProbability

open Lax434930.PolynomialTime

noncomputable def tests {r m : ℕ} (C : System r m) (t k : ℕ)
    (z : Fin (sampleCount t k m) → Fin (r ^ k)) : System (sampleCount t k m) m :=
  sampled (repeated C k) z

def Accept {r m : ℕ} (estimate : Word → ℕ) (C : System r m) (t k : ℕ)
    (z : Fin (sampleCount t k m) → Fin (r ^ k)) : Prop :=
  0 < Fintype.card (Vertex (tests C t k z)) ∧
    threshold m < estimate (EncodedReduction.output (tests C t k z)).encode

def CoinAccept {r m : ℕ} (estimate : Word → ℕ) (C : System r m) (hr : 0 < r) (t k : ℕ)
    (coins : Fin (sampleCount t k m * FreshBitSampling.bitsPerDraw (sampleCount t k m) (r ^ k)) → Bool) :
    Prop := Accept estimate C t k (FreshBitSampling.sampleFlat (pow_pos hr k) coins)

end Lax323828.RandomizedReduction
end
