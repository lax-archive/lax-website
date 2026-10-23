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
end Lax253009.Approximation
end

-- Lax253009.FiniteProbability
section
namespace Lax253009.FiniteProbability

open scoped BigOperators

noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax253009.FiniteProbability
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

-- Lax253009.RandomizedApproximation
section
namespace Lax253009.RandomizedApproximation

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

end Lax253009.RandomizedApproximation
end
