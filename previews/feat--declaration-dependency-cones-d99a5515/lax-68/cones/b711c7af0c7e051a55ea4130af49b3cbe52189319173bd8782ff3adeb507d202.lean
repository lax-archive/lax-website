-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic

-- Lax68.GraphMinors
section
namespace Lax68.GraphMinors.MinorModel
end Lax68.GraphMinors.MinorModel

set_option autoImplicit false

namespace Lax68.GraphMinors

abbrev K5 : SimpleGraph (Fin 5) :=
  SimpleGraph.completeGraph (Fin 5)

abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) :=
  completeBipartiteGraph (Fin 3) (Fin 3)

end Lax68.GraphMinors
end

-- Lax68.GraphTopologicalMinors
section
set_option autoImplicit false

namespace Lax68.GraphTopologicalMinors

def walkInterior {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) : Set V :=
  {x | x ∈ P.support ∧ x ≠ a ∧ x ≠ b}

structure TopologicalMinorModel {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  branch : W ↪ V
  route :
    ∀ {a b : W}, H.Adj a b →
      G.Walk (branch a) (branch b)
  route_isPath :
    ∀ {a b : W} (h : H.Adj a b),
      (route h).IsPath
  branch_avoids_interiors :
    ∀ {a b : W} (h : H.Adj a b) (w : W),
      branch w ∉ walkInterior (route h)
  route_interiors_disjoint :
    ∀ {a b c d : W}
        (hab : H.Adj a b) (hcd : H.Adj c d),
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
        Disjoint
          (walkInterior (route hab))
          (walkInterior (route hcd))

def IsTopologicalMinor {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (TopologicalMinorModel H G)

def IsKuratowskiFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬IsTopologicalMinor Lax68.GraphMinors.K5 G ∧
  ¬IsTopologicalMinor Lax68.GraphMinors.K33 G

end Lax68.GraphTopologicalMinors
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

def HasStraightLineDrawing {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (StraightLineDrawing G)

end Lax68.StraightLineDrawings
end

-- Lax68.Planar
section
set_option autoImplicit false

namespace Lax68.Planar

/-- Existence of a crossing-free straight-line drawing in the real plane. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  StraightLineDrawings.HasStraightLineDrawing G

end Lax68.Planar
end

-- Lax68.KuratowskiPlanarity
section
set_option autoImplicit false

namespace Lax68.KuratowskiPlanarity

axiom planar_iff_kuratowskiFree
    {V : Type*} {G : SimpleGraph V} :
  Finite V →
  (Lax68.Planar.IsPlanar G ↔
    Lax68.GraphTopologicalMinors.IsKuratowskiFree G)

end Lax68.KuratowskiPlanarity
end
