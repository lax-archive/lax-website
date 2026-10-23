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
set_option autoImplicit false

namespace Lax68.StraightLineDrawings

abbrev Point := ℝ × ℝ

structure StraightLineDrawing {V : Type*} (G : SimpleGraph V) where
  point : V → Point
  injective : Function.Injective point
  noVertexOnEdge :
    ∀ {a b c : V},
      G.Adj a b →
      c ≠ a →
      c ≠ b →
      point c ∉ segment ℝ (point a) (point b)
  disjointEdges :
    ∀ {a b c d : V},
      G.Adj a b →
      G.Adj c d →
      Disjoint ({a, b} : Set V) ({c, d} : Set V) →
      Disjoint
        (segment ℝ (point a) (point b))
        (segment ℝ (point c) (point d))

end Lax68.StraightLineDrawings
end

-- Lax68.Outerplanar
section
set_option autoImplicit false

namespace Lax68.Outerplanar

structure OuterplaneDrawing {V : Type*} (G : SimpleGraph V)
    extends StraightLineDrawings.StraightLineDrawing G where
  radius : ℝ
  radius_pos : 0 < radius
  onBoundary :
    ∀ v : V,
      let p := toStraightLineDrawing.point v
      p.1 ^ 2 + p.2 ^ 2 = radius ^ 2

def IsOuterplanar {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (OuterplaneDrawing G)

/-- The usual forbidden-minor characterization of outerplanarity. -/
def IsOuterplanarByExcludedMinors {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ GraphMinors.IsMinor GraphMinors.K4 G ∧
  ¬ GraphMinors.IsMinor GraphMinors.K23 G

end Lax68.Outerplanar
end

-- Lax68.OuterplanarExcludedMinors
section
set_option autoImplicit false

namespace Lax68.OuterplanarExcludedMinors

/-- A finite graph is outerplanar exactly when it has neither `K₄` nor `K₂,₃`
as a minor. This remains open in the present formalization. -/
axiom outerplanar_iff_excludedMinors
    {V : Type*} {G : SimpleGraph V} :
  Finite V →
  (Lax68.Outerplanar.IsOuterplanar G ↔
    Lax68.Outerplanar.IsOuterplanarByExcludedMinors G)

end Lax68.OuterplanarExcludedMinors
end
