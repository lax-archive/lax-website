-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Order.Interval.Set.Basic

-- Lax117284.Scheduling
section
namespace Lax117284
end Lax117284

namespace Lax117284.Scheduling
end Lax117284.Scheduling

namespace Lax117284.Scheduling.Instance
end Lax117284.Scheduling.Instance
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
end

-- Lax117284.Problems
section
namespace Lax117284.Problems
end Lax117284.Problems
end

-- Lax117284.MulticolouredIndepSet
section
namespace Lax117284.MulticolouredIndepSet

open Lax434930.PolynomialTime

/-- An instance of Multicoloured Independent Set: a graph on `colours` classes of `size`
vertices whose edges join vertices of different classes. -/
structure Instance where
  /-- The number `ℓ` of colour classes. -/
  colours : ℕ
  /-- The number `n` of vertices in each class. -/
  size : ℕ
  /-- The graph, on the vertices `(class, index)`. -/
  graph : SimpleGraph (Fin colours × Fin size)
  /-- Adjacent vertices lie in different classes. -/
  adj_colour_ne : ∀ u v, graph.Adj u v → u.1 ≠ v.1

namespace Instance

variable (G : Instance)

/-- The number `ℓn` of vertices. -/
def vertices : ℕ := G.colours * G.size

open Classical in
/-- Whether the vertices numbered `w` and `w'` are adjacent, and `false` for numbers that
name no vertex. -/
noncomputable def adjAt (w w' : ℕ) : Bool :=
  if h : w < G.vertices ∧ w' < G.vertices then
    have hs : 0 < G.size := by
      by_contra h0
      have hz : G.size = 0 := by omega
      rw [vertices, hz, Nat.mul_zero] at h
      omega
    decide (G.graph.Adj
      (⟨w / G.size, (Nat.div_lt_iff_lt_mul hs).2 h.1⟩, ⟨w % G.size, Nat.mod_lt _ hs⟩)
      (⟨w' / G.size, (Nat.div_lt_iff_lt_mul hs).2 h.2⟩, ⟨w' % G.size, Nat.mod_lt _ hs⟩))
  else false

/-- The neighbours of the vertex numbered `w`, in increasing order. -/
noncomputable def nbrs (w : ℕ) : List ℕ :=
  (List.range G.vertices).filter fun w' => G.adjAt w w'

end Instance

end Lax117284.MulticolouredIndepSet
end
