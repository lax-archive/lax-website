-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
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

-- Lax253009.GraphEncoding
section
namespace Lax253009.GraphEncoding

open Graphs

def numbered {α : Type} {n : ℕ} (G : SimpleGraph α) [DecidableRel G.Adj]
    (e : Fin n ≃ α) : Graph n where
  adjacent u v := decide (G.Adj (e u) (e v))
  loopless v := by simp
  symmetric u v := by simp only [G.adj_comm]

axiom cliqueNumber_numbered {α : Type} [Fintype α] {n : ℕ}
    (G : SimpleGraph α) [DecidableRel G.Adj] (e : Fin n ≃ α) :
  (numbered G e).cliqueNumber = G.cliqueNum

end Lax253009.GraphEncoding
end
