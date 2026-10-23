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

abbrev K5 : SimpleGraph (Fin 5) :=
  SimpleGraph.completeGraph (Fin 5)

abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) :=
  completeBipartiteGraph (Fin 3) (Fin 3)

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

-- Lax68.Planar
section
set_option autoImplicit false

namespace Lax68.Planar

def IsPlanarByExcludedMinors {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬GraphMinors.IsMinor GraphMinors.K5 G ∧
  ¬GraphMinors.IsMinor GraphMinors.K33 G

end Lax68.Planar
end
