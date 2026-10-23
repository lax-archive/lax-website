-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange

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
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax762056.GraphEncoding
section
namespace Lax762056.GraphEncoding

open List Turing Lax434930.PolynomialTime

structure Instance where
  order : ℕ
  graph : SimpleGraph (Fin order)
  threshold : ℕ

def unary (n : ℕ) : Word := replicate n true ++ [false]

noncomputable def encode (I : Instance) : Word := by
  classical
  exact unary I.order ++
    (finRange I.order).flatMap (fun u =>
      (finRange I.order).map (fun v => decide (I.graph.Adj u v))) ++
    unary I.threshold

def PolynomialTime (f : Instance → Instance) : Prop :=
  Nonempty (TM2ComputableInPolyTime encode encode f)

end Lax762056.GraphEncoding
end

-- Lax762056.MaxCut
section
namespace Lax762056.MaxCut

open Finset

noncomputable def edges {n : ℕ} (F : SimpleGraph (Fin n)) :
    Finset (Fin n × Fin n) := by
  classical
  exact univ.filter fun e => e.1 < e.2 ∧ F.Adj e.1 e.2

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

noncomputable def offset {n : ℕ} (F : SimpleGraph (Fin n)) : ℕ :=
  2 * ∑ e ∈ edges F, (e.2.val - e.1.val)

end Lax762056.Reduction
end

-- Lax762056.ReductionTime
section
namespace Lax762056.ReductionTime

open GraphEncoding Reduction

axiom reduction_polynomial_time :
  ∃ f : Instance → Instance,
    PolynomialTime f ∧
    ∀ I, Nonempty ((f I).graph ≃g reductionGraph I.graph) ∧
      (f I).threshold = I.threshold + offset I.graph

end Lax762056.ReductionTime
end
