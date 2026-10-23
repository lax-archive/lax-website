-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

-- Lax689614.ArcKayles
section
namespace Lax689614.ArcKayles.Winning
end Lax689614.ArcKayles.Winning

namespace Lax689614.ArcKayles

variable {V : Type} [DecidableEq V]

/-- The position after playing an edge with endpoints `u` and `v`. -/
def remove (S : Finset V) (u v : V) : Finset V := (S.erase u).erase v

/-- Legal moves, represented by ordered pairs of endpoints. -/
noncomputable def moves (G : SimpleGraph V) (S : Finset V) : Finset (V × V) := by
  classical
  exact (S ×ˢ S).filter fun e => G.Adj e.1 e.2

end Lax689614.ArcKayles
end

-- Lax689614.Grundy
section
namespace Lax689614.Grundy

open ArcKayles

noncomputable def mex (S : Finset ℕ) : ℕ := sInf {n : ℕ | n ∉ S}

noncomputable def value {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  mex ((moves G S).attach.image fun e => value G (remove S e.val.1 e.val.2))
termination_by S.card
decreasing_by
  have h := e.property
  simp only [moves, Finset.mem_filter, Finset.mem_product] at h
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem h.1.1)

end Lax689614.Grundy
end

-- Lax689614.Biclique
section
namespace Lax689614.Biclique

def g (a b : ℕ) : ℕ := (a + b) % 2 + 2 * (min a b % 2)

structure Partition {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S L R I : Finset V) : Prop where
  cover : S = L ∪ R ∪ I
  left_right : Disjoint L R
  left_independent : Disjoint L I
  right_independent : Disjoint R I
  left_stable : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v
  right_stable : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v
  independent_stable : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v
  complete : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v
  pendant : ∀ u ∈ L ∪ R, ∃ v ∈ I, G.Adj u v ∧
    ∀ w ∈ S, G.Adj v w → w = u

axiom value_eq {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S L R I : Finset V) (h : Partition G S L R I) :
    Grundy.value G S = g L.card R.card

end Lax689614.Biclique
end
