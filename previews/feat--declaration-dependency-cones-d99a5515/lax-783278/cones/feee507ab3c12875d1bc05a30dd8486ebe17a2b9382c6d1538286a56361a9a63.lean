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
namespace Lax783278
end Lax783278

namespace Lax783278.ArcKayles
end Lax783278.ArcKayles

namespace Lax783278.ArcKayles.WinningAfter
end Lax783278.ArcKayles.WinningAfter
end

-- Lax783278.Grundy
section
namespace Lax783278.Grundy
end Lax783278.Grundy

namespace Lax783278.Grundy.valueAfter
end Lax783278.Grundy.valueAfter
end

-- Lax783278.Biclique
section
namespace Lax783278.Biclique

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

end Lax783278.Biclique
end
