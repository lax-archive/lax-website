-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Card
import Mathlib.Order.Minimal

-- Lax199508.GraphClasses
section
namespace Lax199508
end Lax199508

namespace Lax199508.GraphClasses
end Lax199508.GraphClasses
end

-- Lax199508.UniformQuasiWideness
section
namespace Lax199508.UniformQuasiWideness

open Lax199508.GraphClasses

/-- A set of vertices is distance-`r` independent in `G` when every walk
between two distinct members is longer than `r`. -/
def DistIndependent {V : Type*} (G : SimpleGraph V) (r : ℕ) (A : Set V) : Prop :=
  A.Pairwise fun u v => ∀ p : G.Walk u v, r < p.length

end Lax199508.UniformQuasiWideness
end

-- Lax3.ColoredGraphs
section
namespace Lax3
end Lax3

namespace Lax3.ColoredGraphs
end Lax3.ColoredGraphs
end

-- Lax3.DistFO
section
namespace Lax3.DistFO
end Lax3.DistFO

namespace Lax3.DistFO.DRank
end Lax3.DistFO.DRank

namespace Lax3.DistFO.DistFO
end Lax3.DistFO.DistFO

namespace Lax3.DistFO.IsLocal
end Lax3.DistFO.IsLocal

namespace Lax3.DistFO.Sat
end Lax3.DistFO.Sat

namespace Lax3.DistFO.rename
end Lax3.DistFO.rename

namespace Lax3.DistFO.DistFO.adj
end Lax3.DistFO.DistFO.adj

namespace Lax3.DistFO.DistFO.and
end Lax3.DistFO.DistFO.and

namespace Lax3.DistFO.DistFO.color
end Lax3.DistFO.DistFO.color

namespace Lax3.DistFO.DistFO.distColorLt
end Lax3.DistFO.DistFO.distColorLt

namespace Lax3.DistFO.DistFO.distLe
end Lax3.DistFO.DistFO.distLe

namespace Lax3.DistFO.DistFO.eq
end Lax3.DistFO.DistFO.eq

namespace Lax3.DistFO.DistFO.exL
end Lax3.DistFO.DistFO.exL

namespace Lax3.DistFO.DistFO.exU
end Lax3.DistFO.DistFO.exU

namespace Lax3.DistFO.DistFO.not
end Lax3.DistFO.DistFO.not
end

-- Lax3.ScatterSentences
section
namespace Lax3.ScatterSentences.ScatterSentence
end Lax3.ScatterSentences.ScatterSentence

namespace Lax3.ScatterSentences

open Lax3.ColoredGraphs Lax3.DistFO Lax199508.UniformQuasiWideness

/-- A choice of scatter values: for every graph `G`, radius `r` and
vertex set `X`, a number `size G r X` which is the cardinality of some
inclusion-wise maximal `r`-scattered subset of `X`. This is the
source's "fix arbitrarily and once and for all a value `s`", made a
parameter: every statement about scatter sentences holds for every
choice. -/
structure ScatterChoice where
  /-- The chosen scatter value of a graph, radius and vertex set. -/
  size : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ → Set (Fin n) → ℕ
  /-- The chosen value is realized by an inclusion-wise maximal
  `r`-scattered subset of `X`. -/
  spec : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)),
    ∃ S : Set (Fin n), S ⊆ X ∧
      Maximal (fun T => T ⊆ X ∧ DistIndependent G r T) S ∧ S.ncard = size G r X

variable {L n : ℕ}

end Lax3.ScatterSentences
end
