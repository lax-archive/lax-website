-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange

-- Lax762056.InducedMinors
section
namespace Lax762056.InducedMinors

open SimpleGraph

structure Model {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) where
  branch : W → Set V
  connected : ∀ v, Connected (G.induce (branch v))
  disjoint : ∀ u v, u ≠ v → Disjoint (branch u) (branch v)
  adjacent : ∀ u v, u ≠ v →
    (H.Adj u v ↔ ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y)

def IsInducedMinor {W V : Type*} (H : SimpleGraph W)
    (G : SimpleGraph V) : Prop :=
  Nonempty (Model H G)

end Lax762056.InducedMinors
end

-- Lax762056.Grid
section
namespace Lax762056.Grid

open SimpleGraph InducedMinors

def squareGrid (k : ℕ) : SimpleGraph (Fin k × Fin k) :=
  (pathGraph k).boxProd (pathGraph k)

def ExcludesInducedGrid (k : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ IsInducedMinor (squareGrid k) G

end Lax762056.Grid
end

-- Lax762056.ColumnGraph
section
namespace Lax762056.ColumnGraph

open SimpleGraph

abbrev Vertex (R : Type*) (c : ℕ) := R × Fin c × Bool

def columnGraph (R : Type*) (c : ℕ) : SimpleGraph (Vertex R c) :=
  fromRel fun (row, column, side) (row', column', side') =>
    (column = column' ∧ side ≠ side') ∨
    (row = row' ∧ (column.val + 1 = column'.val ∨ column'.val + 1 = column.val))

end Lax762056.ColumnGraph
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax762056.GraphEncoding
section
namespace Lax762056
end Lax762056

namespace Lax762056.GraphEncoding
end Lax762056.GraphEncoding

namespace Lax762056.GraphEncoding.Instance
end Lax762056.GraphEncoding.Instance
end

-- Lax762056.MaxCut
section
namespace Lax762056.MaxCut
end Lax762056.MaxCut
end

-- Lax762056.Reduction
section
namespace Lax762056.Reduction

open ColumnGraph MaxCut

abbrev Edge {n : ℕ} (F : SimpleGraph (Fin n)) :=
  {e : Fin n × Fin n // e.1 < e.2 ∧ F.Adj e.1 e.2}

abbrev Row {n : ℕ} (F : SimpleGraph (Fin n)) := Edge F × Bool

abbrev Vertex {n : ℕ} (F : SimpleGraph (Fin n)) :=
  ColumnGraph.Vertex (Row F) (2 * n - 1)

def retainedVertices {n : ℕ} (F : SimpleGraph (Fin n)) : Set (Vertex F) :=
  fun ((edge, tag), column, side) =>
    let u := edge.val.1.val
    let v := edge.val.2.val
    let j := column.val
    (j = 2 * u ∧ side = tag) ∨
    (2 * u < j ∧ j < 2 * v) ∨
    (j = 2 * v ∧ side = !tag)

def reductionGraph {n : ℕ} (F : SimpleGraph (Fin n)) :
    SimpleGraph (retainedVertices F) :=
  (columnGraph (Row F) (2 * n - 1)).induce (retainedVertices F)

end Lax762056.Reduction
end

-- Lax762056.GridExclusion
section
namespace Lax762056.GridExclusion

open Grid Reduction

axiom reduction_excludes_inducedGrid {n : ℕ} (F : SimpleGraph (Fin n)) :
  ExcludesInducedGrid 5 (reductionGraph F)

end Lax762056.GridExclusion
end
