-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Lattice
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

-- Lax228581.Treewidth
section
namespace Lax228581
end Lax228581

namespace Lax228581.Treewidth
end Lax228581.Treewidth

namespace Lax228581.Treewidth.TreeDecomposition
end Lax228581.Treewidth.TreeDecomposition
end

-- Lax117284.ConflictGraph
section
namespace Lax117284.ConflictGraph
end Lax117284.ConflictGraph
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

/-- The class of the vertex numbered `w`. -/
def classOf (w : ℕ) : ℕ := w / G.size

/-- The index inside its class of the vertex numbered `w`. -/
def indexOf (w : ℕ) : ℕ := w % G.size

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

/-- The number of neighbours the vertex `0` has; on a regular graph, the degree `r`. -/
noncomputable def degree : ℕ := (G.nbrs 0).length

/-- The edges, each listed as the pair of its endpoints from the smaller number to the
larger — which, since adjacent vertices lie in different classes, is from the smaller class
to the larger. -/
noncomputable def edgeList : List (ℕ × ℕ) :=
  (List.range G.vertices).flatMap fun w => ((G.nbrs w).filter fun w' => w < w').map (w, ·)

end Instance

end Lax117284.MulticolouredIndepSet
end

-- Lax117284.Lemma14
section
namespace Lax117284.Lemma14

open Lax117284.Problems Lax117284.MulticolouredIndepSet

open Lax434930.PolynomialTime Lax429075.Reductions

variable (G : Instance)

/-- The degree of the graph, read off the vertex `0` and raised to `1`. -/
noncomputable def deg : ℕ := max 1 G.degree

/-- The number `N` of clients other than the dummy client, which is the length of its job
and the number of time units inside it. -/
noncomputable def span : ℕ := 2 + G.colours + G.vertices + G.vertices * deg G

/-- The number of the selection client of colour `i`. -/
def selId (i : ℕ) : ℕ := 3 + i

/-- The number of the vertex client of the vertex numbered `w`. -/
def vtxId (w : ℕ) : ℕ := 3 + G.colours + w

/-- The number of the edge client `c_{v,u}` where `v` is the vertex numbered `w` and `u` is
its `q`'th neighbour. -/
noncomputable def incId (w q : ℕ) : ℕ :=
  3 + G.colours + G.vertices + w * deg G + q

/-- The processing time and the due date of client `c` on the vertex day of the vertex
numbered `w₀`. -/
noncomputable def vertexDay (w₀ c : ℕ) : ℕ × ℕ :=
  if c = 0 then (span G, deg G + span G)
  else if c = vtxId G w₀ ∨ c = selId (G.classOf w₀) then (deg G, deg G)
  else (1, deg G + c)

/-- The processing time and the due date of client `c` on the validation day of colour
`i₀`. -/
noncomputable def validationDay (i₀ c : ℕ) : ℕ × ℕ :=
  if c = 0 then (span G, deg G * G.size + span G)
  else if 3 + G.colours ≤ c ∧ c < 3 + G.colours + G.vertices ∧
      G.classOf (c - (3 + G.colours)) = i₀ then
    (deg G, deg G * (G.indexOf (c - (3 + G.colours)) + 1))
  else if 3 + G.colours + G.vertices ≤ c ∧
      G.classOf ((c - (3 + G.colours + G.vertices)) / deg G) = i₀ then
    (1, deg G * G.indexOf ((c - (3 + G.colours + G.vertices)) / deg G)
      + (c - (3 + G.colours + G.vertices)) % deg G + 1)
  else (1, deg G * G.size + c)

/-- The processing time and the due date of client `c` on the edge day of the edge from the
vertex numbered `w` to the vertex numbered `w'`. -/
noncomputable def edgeDay (w w' c : ℕ) : ℕ × ℕ :=
  if c = 0 then (span G, 3 + span G)
  else if c = 2 then (2, 2)
  else if c = 1 then (2, 3)
  else if c = incId G w ((G.nbrs w).idxOf w') then (1, 3)
  else if c = incId G w' ((G.nbrs w').idxOf w) then (1, 1)
  else (1, 3 + c)

/-- The processing time and the due date of client `c` on day `i`: the colour blocks of `n`
vertex days and a validation day come first, then the edge days. -/
noncomputable def job (i c : ℕ) : ℕ × ℕ :=
  if i < G.colours * (G.size + 1) then
    (if i % (G.size + 1) < G.size then
      vertexDay G ((i / (G.size + 1)) * G.size + i % (G.size + 1)) c
    else validationDay G (i / (G.size + 1)) c)
  else
    edgeDay G (G.edgeList.getD (i - G.colours * (G.size + 1)) (0, 0)).1
      (G.edgeList.getD (i - G.colours * (G.size + 1)) (0, 0)).2 c

theorem one_le_deg : 1 ≤ deg G := le_max_left 1 _

theorem two_le_span : 2 ≤ span G := by unfold span; omega

theorem job_pos (i c : ℕ) : 0 < (job G i c).1 := by
  have hd := one_le_deg G
  have hs := two_le_span G
  unfold job vertexDay validationDay edgeDay
  split_ifs <;> simp only [] <;> omega

end Lax117284.Lemma14
end
