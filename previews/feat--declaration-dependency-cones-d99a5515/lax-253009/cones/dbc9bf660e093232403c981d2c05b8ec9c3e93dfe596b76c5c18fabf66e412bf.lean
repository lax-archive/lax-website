-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.FinRange

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

noncomputable def Graph.cliqueNumber {n : ℕ} (G : Graph n) : ℕ :=
  G.simpleGraph.cliqueNum

end Lax253009.Graphs
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax253009.Approximation
section
namespace Lax253009.Approximation
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

noncomputable def System.acceptedSeeds {r m : ℕ} (C : System r m)
    (π : Oracle m) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter fun seed ↦ ∃ a ∈ C.accepting seed, Extends π a

noncomputable def System.optimum {r m : ℕ} (C : System r m) : ℕ :=
  Finset.univ.sup fun π : Oracle m ↦ (C.acceptedSeeds π).card

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

axiom cliqueNumber_output {r m : ℕ} (C : System r m) :
  (output C).cliqueNumber = C.optimum

end Lax253009.EncodedReduction
end
