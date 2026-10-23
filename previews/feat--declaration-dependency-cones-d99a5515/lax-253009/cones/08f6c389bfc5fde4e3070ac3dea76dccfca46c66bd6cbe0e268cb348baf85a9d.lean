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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
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

-- Lax253009.LongCode
section
namespace Lax253009.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

abbrev Table (w : ℕ) := Coordinate w → Bool

def compose {w s : ℕ} (f : Fin s → Coordinate w) (B : Word s → Bool) : Coordinate w :=
  fun x ↦ B (fun i ↦ f i x)

def Accepts {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w) : Prop :=
  ∀ B : Word s → Bool, A (compose f B) = B (fun i ↦ A (f i))

def AgreesOn {w : ℕ} (h g g' : Coordinate w) : Prop :=
  ∀ x, h x = true → g x = g' x

def Queried {w s : ℕ} (f : Fin s → Coordinate w) (g : Coordinate w) : Prop :=
  (∃ i, g = f i) ∨ ∃ B : Word s → Bool, g = compose f B

def AcceptsWithCondition {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) : Prop :=
  Accepts A f ∧ ∀ g, Queried f g → ∀ g', AgreesOn h g g' → A g = A g'

end Lax253009.LongCode
end

-- Lax253009.CNASoundness
section
namespace Lax253009.CNASoundness
end Lax253009.CNASoundness
end

-- Lax253009.ManyTableConsistency
section
namespace Lax253009.ManyTableConsistency
end Lax253009.ManyTableConsistency
end

-- Lax253009.FAFTest
section
namespace Lax253009.FAFTest
end Lax253009.FAFTest
end

-- Lax253009.LongCodePatterns
section
namespace Lax253009.LongCodePatterns

open LongCode

abbrev Pattern (w : ℕ) := Coordinate w → Option Bool

noncomputable def restrict {w : ℕ} (Q : Coordinate w → Prop) (A : Table w) :
    Pattern w := by
  classical
  exact fun g ↦ if Q g then some (A g) else none

def SideQueried {w s : ℕ} (f : Fin s → Coordinate w) (h g' : Coordinate w) : Prop :=
  ∃ g, Queried f g ∧ AgreesOn h g g'

noncomputable def sidePatterns {w s : ℕ} (f : Fin s → Coordinate w)
    (h : Coordinate w) : Finset (Pattern w) := by
  classical
  exact (Finset.univ.filter (fun A : Table w ↦ AcceptsWithCondition A f h)).image
    (restrict (SideQueried f h))

end Lax253009.LongCodePatterns
end

-- Lax253009.FAFPatterns
section
namespace Lax253009.FAFPatterns

open LongCode LongCodePatterns

noncomputable def conditionOfAnswers {Ω : Type} {u w q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Ω) (g : Fin q → Coordinate u) (b : Word q) : Coordinate w :=
  fun y ↦ valid ω y && decide (∀ j, g j (ρ ω y) = b j)

noncomputable def patterns {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    Finset (Word q × (Fin n → Pattern w)) := by
  classical
  exact Finset.univ.biUnion (fun b : Word q ↦
    (Fintype.piFinset (fun i ↦ sidePatterns (f i) (conditionOfAnswers ρ valid (ω i) g b))).image
      (fun a ↦ (b, a)))

end Lax253009.FAFPatterns
end

-- Lax253009.DecodedStrategies
section
namespace Lax253009.DecodedStrategies

open FiniteProbability

def Wins {U Ω W X Y : Type}
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (P : W → Option Y) (Q : U → Option X) (z : U × Ω) : Prop :=
  ∃ y x, P (question z.1 z.2) = some y ∧ Q z.1 = some x ∧ V z.1 z.2 y x

end Lax253009.DecodedStrategies
end

-- Lax253009.FAFStrategyExtraction
section
namespace Lax253009.FAFStrategyExtraction

open LongCode FiniteProbability

abbrev Seed (Ω : Type) (u w n s q : ℕ) :=
  ((Fin n → Ω) × (Fin q → Coordinate u)) × (Fin n → Fin s → Coordinate w)

def Relation {U Ω : Type} {u w : ℕ}
    (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
    (v : U) (ω : Ω) (y : Word w) (x : Word u) : Prop :=
  valid v ω y = true ∧ ρ v ω y = x

end Lax253009.FAFStrategyExtraction
end

-- Lax253009.FAFComposition
section
namespace Lax253009.FAFComposition

open LongCode FiniteProbability FAFStrategyExtraction

noncomputable def gameThreshold (l s : ℕ) : ℝ :=
  ((1 / 2 : ℝ) ^ (20 * l * l * s) / 2) * (1 / 2 : ℝ) ^ (20 * l * s) /
    ((2 : ℝ) ^ s + 1)

end Lax253009.FAFComposition
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

abbrev View (m : ℕ) := Fin m → Option Bool

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

-- Lax253009.FAFLocalTests
section
namespace Lax253009.FAFLocalTests

open LongCode LocalTests LongCodePatterns TestRepetition TestSampling

abbrev Index (U W : Type) (u w : ℕ) := (U × Coordinate u) ⊕ (W × Coordinate w)

abbrev Randomness (U Ω : Type) (u w n s q : ℕ) :=
  U × FAFStrategyExtraction.Seed Ω u w n s q

noncomputable def indexEquiv (U W : Type) [Fintype U] [Fintype W] (u w : ℕ) :
    Index U W u w ≃ Fin (Fintype.card (Index U W u w)) := Fintype.equivFin _

noncomputable def randomEquiv (U Ω : Type) [Fintype U] [Fintype Ω] (u w n s q : ℕ) :
    Randomness U Ω u w n s q ≃ Fin (Fintype.card (Randomness U Ω u w n s q)) :=
  Fintype.equivFin _

noncomputable def parts {U Ω W : Type} [Fintype U] [Fintype W] {u w n s q : ℕ}
    (question : U → Ω → W) (z : Randomness U Ω u w n s q)
    (p : LongCode.Word q × (Fin n → Pattern w)) :
    Fin (q + n) → View (Fintype.card (Index U W u w)) := by
  classical
  exact Fin.addCases
    (fun j x ↦ if x = indexEquiv U W u w (Sum.inl (z.1, z.2.1.2 j)) then some (p.1 j) else none)
    (fun i x ↦ match (indexEquiv U W u w).symm x with
      | .inl _ => none
      | .inr (v, g) => if v = question z.1 (z.2.1.1 i) then p.2 i g else none)

noncomputable def system {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w) :
    System (Fintype.card (Randomness U Ω u w n s q)) (Fintype.card (Index U W u w)) := by
  classical
  exact ⟨fun seed ↦
    let z := (randomEquiv U Ω u w n s q).symm seed
    ((FAFPatterns.patterns (ρ z.1) (valid z.1) z.2.1.1 z.2.1.2 z.2.2).filter
      (fun p ↦ Coherent (parts question z p))).image (fun p ↦ merge (parts question z p))⟩

end Lax253009.FAFLocalTests
end

-- Lax253009.FreshBitSampling
section
namespace Lax253009.FreshBitSampling

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

end Lax253009.FreshBitSampling
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

def CoinAccept {r m : ℕ} (estimate : Word → ℕ) (C : System r m) (hr : 0 < r) (t k : ℕ)
    (coins : Fin (sampleCount t k m * FreshBitSampling.bitsPerDraw (sampleCount t k m) (r ^ k)) → Bool) :
    Prop := Accept estimate C t k (FreshBitSampling.sampleFlat (pow_pos hr k) coins)

end Lax253009.RandomizedReduction
end

-- Lax253009.GameToClique
section
namespace Lax253009.GameToClique

open LocalTests ConsistencyGraph TestSampling SamplingParameters FiniteProbability

open Lax434930.PolynomialTime

axiom reduction (ε : ℝ) (hε : 0 < ε) (happrox : Approximation.Approximable ε) :
  ∃ estimate : Word → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
    ∃ l s c w₀ : ℕ, 0 < l ∧ 0 < s ∧ 0 < c ∧
    ∀ w : ℕ, w₀ ≤ w →
    ∀ {U Ω W : Type} [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
      [Fintype W] [DecidableEq W],
    ∀ u : ℕ, ∀ (question : U → Ω → W)
      (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → LongCode.Coordinate w),
      let C := FAFLocalTests.system (n := 10 * l) (s := s) (q := 10 * l * s) question ρ valid
      let m := Fintype.card (FAFLocalTests.Index U W u w)
      let k := repetitions c m
      (∀ (P : W → LongCode.Word w) (Q : U → LongCode.Word u),
        (∀ v ω, valid v ω (P (question v ω)) = true) →
        (∀ v ω, ρ v ω (P (question v ω)) = Q v) →
        ∀ coins, RandomizedReduction.CoinAccept estimate C (by exact Fintype.card_pos)
          (20 * l * l * s) k coins) ∧
      ((∀ (P : W → Option (LongCode.Word w)) (Q : U → Option (LongCode.Word u)),
        probability (DecodedStrategies.Wins question (FAFStrategyExtraction.Relation ρ valid) P Q) <
          FAFComposition.gameThreshold l s) →
        probability (RandomizedReduction.CoinAccept estimate C (by exact Fintype.card_pos)
          (20 * l * l * s) k) ≤ 1 / 3) ∧
      (∀ z, Fintype.card (Vertex (RandomizedReduction.tests C (20 * l * l * s) k z)) ≤
        16 ^ ((20 * l * l * s + 20 * l * s) * c) *
          (m + 2) ^ ((20 * l * l * s + 20 * l * s) * c + 1))

end Lax253009.GameToClique
end
