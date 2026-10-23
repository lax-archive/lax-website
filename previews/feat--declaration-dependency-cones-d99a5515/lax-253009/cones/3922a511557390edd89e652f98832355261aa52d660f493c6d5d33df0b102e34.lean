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

-- Lax253009.FiniteProbability
section
namespace Lax253009.FiniteProbability

open scoped BigOperators

noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax253009.FiniteProbability
end

-- Lax253009.FreshBitSampling
section
namespace Lax253009.FreshBitSampling
end Lax253009.FreshBitSampling
end

-- Lax253009.BernoulliSampling
section
namespace Lax253009.BernoulliSampling
end Lax253009.BernoulliSampling
end

-- Lax253009.Graphs
section
namespace Lax253009.Graphs

structure Graph (n : ℕ) where
  adjacent : Fin n → Fin n → Bool
  loopless : ∀ v, adjacent v v = false
  symmetric : ∀ u v, adjacent u v = adjacent v u

def Graph.simpleGraph {n : ℕ} (G : Graph n) : SimpleGraph (Fin n) where
  Adj u v := G.adjacent u v = true
  symm := ⟨fun u v h ↦ by rw [← G.symmetric]; exact h⟩
  loopless := ⟨fun v ↦ by simp [G.loopless]⟩

def Graph.encode {n : ℕ} (G : Graph n) : List Bool :=
  List.replicate n true ++ [false] ++
    (List.finRange n).flatMap (fun u ↦ (List.finRange n).map (G.adjacent u))

noncomputable def Graph.cliqueNumber {n : ℕ} (G : Graph n) : ℕ :=
  G.simpleGraph.cliqueNum

end Lax253009.Graphs
end

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax253009.Approximation
section
namespace Lax253009.Approximation

open Graphs

open Lax434930.PolynomialTime

def Approximable (ε : ℝ) : Prop :=
  ∃ estimate : Word → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
    ∀ (n : ℕ), 0 < n → ∀ G : Graph n,
      estimate G.encode ≤ G.cliqueNumber ∧
      (G.cliqueNumber : ℝ) ≤ Real.rpow (n : ℝ) (1 - ε) * (estimate G.encode : ℝ)

end Lax253009.Approximation
end

-- Lax253009.LocalTests
section
namespace Lax253009.LocalTests

abbrev Oracle (m : ℕ) := Fin m → Bool

abbrev View (m : ℕ) := Fin m → Option Bool

def Extends {m : ℕ} (π : Oracle m) (a : View m) : Prop :=
  ∀ i b, a i = some b → π i = b

def Compatible {m : ℕ} (a b : View m) : Prop :=
  ∀ i x y, a i = some x → b i = some y → x = y

structure System (r m : ℕ) where
  accepting : Fin r → Finset (View m)

end Lax253009.LocalTests
end

-- Lax253009.ConsistencyGraph
section
namespace Lax253009.ConsistencyGraph

open LocalTests

abbrev Vertex {r m : ℕ} (C : System r m) :=
  (seed : Fin r) × {a // a ∈ C.accepting seed}

def graph {r m : ℕ} (C : System r m) : SimpleGraph (Vertex C) where
  Adj u v := u.1 ≠ v.1 ∧ Compatible u.2.1 v.2.1
  symm := ⟨fun _ _ h ↦ ⟨Ne.symm h.1,
    fun i x y hx hy ↦ (h.2 i y x hy hx).symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

end Lax253009.ConsistencyGraph
end

-- Lax253009.CliqueCorrespondence
section
namespace Lax253009.CliqueCorrespondence
end Lax253009.CliqueCorrespondence
end

-- Lax253009.GraphEncoding
section
namespace Lax253009.GraphEncoding

open Graphs

def numbered {α : Type} {n : ℕ} (G : SimpleGraph α) [DecidableRel G.Adj]
    (e : Fin n ≃ α) : Graph n where
  adjacent u v := decide (G.Adj (e u) (e v))
  loopless v := by simp
  symmetric u v := by simp only [G.adj_comm]

end Lax253009.GraphEncoding
end

-- Lax253009.EncodedReduction
section
namespace Lax253009.EncodedReduction

open LocalTests ConsistencyGraph Lax434930.PolynomialTime

noncomputable def output {r m : ℕ} (C : System r m) :
    Graphs.Graph (Fintype.card (Vertex C)) := by
  classical
  exact GraphEncoding.numbered (graph C) (Fintype.equivFin (Vertex C)).symm

end Lax253009.EncodedReduction
end

-- Lax253009.TestSampling
section
namespace Lax253009.TestSampling

open LocalTests FiniteProbability ConsistencyGraph

def Passes {r m : ℕ} (C : System r m) (π : Oracle m) (seed : Fin r) : Prop :=
  ∃ a ∈ C.accepting seed, Extends π a

def Complete {r m : ℕ} (C : System r m) : Prop := ∃ π, ∀ seed, Passes C π seed

def Sound {r m : ℕ} (C : System r m) (p : ℝ) : Prop :=
  ∀ π, probability (Passes C π) ≤ p

def sampled {r m N : ℕ} (C : System r m) (z : Fin N → Fin r) : System N m :=
  ⟨fun i ↦ C.accepting (z i)⟩

end Lax253009.TestSampling
end

-- Lax253009.TestRepetition
section
namespace Lax253009.TestRepetition

open LocalTests TestSampling FiniteProbability

def Coherent {m k : ℕ} (a : Fin k → View m) : Prop :=
  ∀ i j, Compatible (a i) (a j)

def merge {m : ℕ} : {k : ℕ} → (Fin k → View m) → View m
  | 0, _ => fun _ ↦ none
  | k + 1, a => fun i ↦ (a 0 i).or (merge (fun j : Fin k ↦ a j.succ) i)

noncomputable def seedEquiv (r k : ℕ) : (Fin k → Fin r) ≃ Fin (r ^ k) :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def repeated {r m : ℕ} (C : System r m) (k : ℕ) : System (r ^ k) m := by
  classical
  exact ⟨fun z ↦ ((Fintype.piFinset (fun i : Fin k ↦ C.accepting ((seedEquiv r k).symm z i))).filter
    Coherent).image merge⟩

end Lax253009.TestRepetition
end

-- Lax253009.SamplingParameters
section
namespace Lax253009.SamplingParameters

def repetitions (c m : ℕ) : ℕ := c * (Nat.clog 2 (m + 2) + 3)

def sampleCount (t k m : ℕ) : ℕ := (m + 2) * 2 ^ (t * k)

def threshold (m : ℕ) : ℕ := 4 * (m + 2)

end Lax253009.SamplingParameters
end

-- Lax253009.RandomizedReduction
section
namespace Lax253009.RandomizedReduction

open LocalTests ConsistencyGraph TestSampling TestRepetition SamplingParameters FiniteProbability

open Lax434930.PolynomialTime

noncomputable def tests {r m : ℕ} (C : System r m) (t k : ℕ)
    (z : Fin (sampleCount t k m) → Fin (r ^ k)) : System (sampleCount t k m) m :=
  sampled (repeated C k) z

def Accept {r m : ℕ} (estimate : Word → ℕ) (C : System r m) (t k : ℕ)
    (z : Fin (sampleCount t k m) → Fin (r ^ k)) : Prop :=
  0 < Fintype.card (Vertex (tests C t k z)) ∧
    threshold m < estimate (EncodedReduction.output (tests C t k z)).encode

axiom approximation_decision (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (happrox : Approximation.Approximable ε) :
  ∃ estimate : Word → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
    ∀ (f t c : ℕ), 1 ≤ (c : ℝ) * ((t : ℝ) * ε - (f : ℝ) * (1 - ε)) →
    ∀ (r m : ℕ), 0 < r → ∀ C : System r m,
      (∀ seed, (C.accepting seed).card ≤ 2 ^ f) →
      (Complete C → ∀ z, Accept estimate C t (repetitions c m) z) ∧
      (Sound C ((1 / 2 : ℝ) ^ t) →
        probability (Accept estimate C t (repetitions c m)) ≤ 1 / 4)

end Lax253009.RandomizedReduction
end
