-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

-- Lax783278.ArcKayles
section
namespace Lax783278.ArcKayles.WinningAfter
end Lax783278.ArcKayles.WinningAfter

namespace Lax783278.ArcKayles

open scoped Classical

variable {V : Type} [DecidableEq V]

/-- The position after playing an edge with endpoints `u` and `v`. -/
def remove (S : Finset V) (u v : V) : Finset V := (S.erase u).erase v

/-- Legal moves, represented by ordered pairs of endpoints. -/
noncomputable def moves (G : SimpleGraph V) (S : Finset V) : Finset (V × V) :=
  (S ×ˢ S).filter fun e => G.Adj e.1 e.2

end Lax783278.ArcKayles
end

-- Lax783278.Grundy
section
namespace Lax783278.Grundy

open ArcKayles

/-- The least natural number not in the finite set `S`. -/
noncomputable def mex (S : Finset ℕ) : ℕ := sInf {n : ℕ | n ∉ S}

/-- The game value obtained from `rounds` rounds of backward induction.
A position at depth zero has value zero; each further round takes the
minimum excluded value of its immediate successors. -/
noncomputable def valueAfter {V : Type} [DecidableEq V]
    (G : SimpleGraph V) : ℕ → Finset V → ℕ
  | 0, _ => 0
  | rounds + 1, S =>
      mex ((moves G S).image fun e => valueAfter G rounds (remove S e.1 e.2))

/-- The Sprague–Grundy value of the complete game tree. Its depth is at most
the number of surviving vertices, because every move removes two vertices. -/
noncomputable def value {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  valueAfter G S.card S

end Lax783278.Grundy
end

-- Lax783278.Biclique
section
namespace Lax783278.Biclique

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

end Lax783278.Biclique
end
