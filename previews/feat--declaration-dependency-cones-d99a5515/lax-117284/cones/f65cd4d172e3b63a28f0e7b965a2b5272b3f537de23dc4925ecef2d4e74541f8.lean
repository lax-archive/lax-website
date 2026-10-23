-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

-- Lax271696.GraphEncoding
section
namespace Lax271696
end Lax271696

namespace Lax271696.GraphEncoding
end Lax271696.GraphEncoding

namespace Lax271696.GraphEncoding.EncodesGraph
end Lax271696.GraphEncoding.EncodesGraph
end

-- Lax117284.BipartiteGraph
section
namespace Lax117284
end Lax117284

namespace Lax117284.BipartiteGraph
end Lax117284.BipartiteGraph
end

-- Lax117284.BipartiteKuhn
section
namespace Lax117284
end Lax117284

namespace Lax117284.BipartiteKuhn
end Lax117284.BipartiteKuhn

namespace Lax117284.BipartiteKuhn.runAll
end Lax117284.BipartiteKuhn.runAll

namespace Lax117284.BipartiteKuhn.step
end Lax117284.BipartiteKuhn.step

namespace Lax117284.BipartiteKuhn.tryAugment
end Lax117284.BipartiteKuhn.tryAugment
end

-- Lax117284.BipartiteMatching
section
namespace Lax117284
end Lax117284

namespace Lax117284.BipartiteMatching
end Lax117284.BipartiteMatching
end

-- Lax117284.BipartiteKuhnCorrect
section
namespace Lax117284.BipartiteKuhnCorrect

open Lax117284.BipartiteKuhn Lax117284.BipartiteMatching Lax117284.BipartiteGraph

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (adj : L → R → Prop) [DecidableRel adj]

/-- The adjacency across the split of a graph on `Fin V` split at `n`, as a relation between
the left vertices `Fin n` and the right vertices `Fin (V - n)`. -/
def leftRel {V : ℕ} (G : SimpleGraph (Fin V)) (n : ℕ) (hn : n ≤ V) :
    Fin n → Fin (V - n) → Prop :=
  fun i j => G.Adj ⟨i, by omega⟩ ⟨n + j, by omega⟩

end Lax117284.BipartiteKuhnCorrect
end
