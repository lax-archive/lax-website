-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic

-- Lax68.GraphMinors
section
set_option autoImplicit false

namespace Lax68.GraphMinors

structure MinorModel {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  branchSet : W → Set V
  connected : ∀ w, (G.induce (branchSet w)).Connected
  disjoint :
    ∀ {u v}, u ≠ v →
      Disjoint (branchSet u) (branchSet v)
  adjacent :
    ∀ {u v}, H.Adj u v →
      ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y

def IsMinor {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (MinorModel H G)

abbrev K4 : SimpleGraph (Fin 4) :=
  SimpleGraph.completeGraph (Fin 4)

abbrev K23 : SimpleGraph (Fin 2 ⊕ Fin 3) :=
  completeBipartiteGraph (Fin 2) (Fin 3)

end Lax68.GraphMinors
end

-- Lax68.StraightLineDrawings
section
namespace Lax68
end Lax68

namespace Lax68.StraightLineDrawings
end Lax68.StraightLineDrawings

namespace Lax68.StraightLineDrawings.StraightLineDrawing
end Lax68.StraightLineDrawings.StraightLineDrawing
end

-- Lax68.Outerplanar
section
namespace Lax68.Outerplanar.OuterplaneDrawing
end Lax68.Outerplanar.OuterplaneDrawing

set_option autoImplicit false

namespace Lax68.Outerplanar

/-- The usual forbidden-minor characterization of outerplanarity. -/
def IsOuterplanarByExcludedMinors {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ GraphMinors.IsMinor GraphMinors.K4 G ∧
  ¬ GraphMinors.IsMinor GraphMinors.K23 G

end Lax68.Outerplanar
end
