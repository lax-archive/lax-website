-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image

-- Lax3.ColoredGraphs
section
namespace Lax3
end Lax3

namespace Lax3.ColoredGraphs
end Lax3.ColoredGraphs
end

-- Lax3.DistFO
section
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

namespace Lax3.DistFO

open Lax3.ColoredGraphs

variable {L n : ℕ}

/-- The vertices `u` and `v` are within distance `d` *inside* `D`: some
walk from `u` to `v` has length at most `d` and stays in `D`. This is
the walk distance of the substructure induced on `D`, with the carrier
kept. -/
def WithinDistIn {V : Type*} (D : Set V) (G : SimpleGraph V) (d : ℕ) (u v : V) : Prop :=
  ∃ w : G.Walk u v, w.length ≤ d ∧ ∀ x ∈ w.support, x ∈ D

end Lax3.DistFO
end
