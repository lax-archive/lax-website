-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Prod

-- Lax17.Grid
section
namespace Lax17.Grid

/-- The canonical `g × g` square grid. -/
def squareGrid (g : ℕ) : SimpleGraph (Fin g × Fin g) :=
  SimpleGraph.pathGraph g □ SimpleGraph.pathGraph g

end Lax17.Grid
end

-- Lax17.Minor
section
namespace Lax17.Minor

universe u v

/-- Branch-set data witnessing that `H` is a minor of `G`. -/
structure Model {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set representing each vertex of `H`. -/
  branchSet : W → Set V
  /-- Every branch set is nonempty. -/
  branch_nonempty : ∀ w : W, (branchSet w).Nonempty
  /-- Every branch set induces a connected graph in `G`. -/
  branch_connected :
    ∀ w : W, (G.induce (branchSet w)).Connected
  /-- Branch sets representing distinct vertices are disjoint. -/
  branch_disjoint :
    ∀ ⦃x y : W⦄, x ≠ y → Disjoint (branchSet x) (branchSet y)
  /-- Every edge of `H` is represented by an edge between branch sets. -/
  adjacent :
    ∀ ⦃x y : W⦄, H.Adj x y →
      ∃ a ∈ branchSet x, ∃ b ∈ branchSet y, G.Adj a b

/-- `H` is a graph minor of `G`. -/
def IsMinor {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (Model H G)

end Lax17.Minor
end

-- Lax17.GridMinor
section
namespace Lax17.GridMinor

universe u

/-- `G` contains the `g × g` square grid as a minor. -/
def ContainsGridMinor {V : Type u} (G : SimpleGraph V) (g : ℕ) : Prop :=
  Lax17.Minor.IsMinor (Lax17.Grid.squareGrid g) G

end Lax17.GridMinor
end

-- Lax17.Treewidth
section
namespace Lax17.Treewidth

universe u

/-- A finite tree decomposition of a simple graph. -/
structure TreeDecomposition {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) where
  /-- The node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree has finitely many nodes. -/
  [nodeFintype : Fintype Node]
  /-- Decomposition-tree nodes have decidable equality. -/
  [nodeDecidableEq : DecidableEq Node]
  /-- The tree on decomposition nodes. -/
  tree : SimpleGraph Node
  /-- The node graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag assigned to each decomposition node. -/
  bag : Node → Finset V
  /-- Every graph vertex occurs in a bag. -/
  vertex_mem_bag : ∀ v : V, ∃ i : Node, v ∈ bag i
  /-- The endpoints of every graph edge occur together in a bag. -/
  edge_mem_bag :
    ∀ ⦃x y : V⦄, G.Adj x y → ∃ i : Node, x ∈ bag i ∧ y ∈ bag i
  /-- Bags containing a fixed graph vertex induce a connected subtree. -/
  bag_indices_connected :
    ∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected

namespace TreeDecomposition

/-- The maximum bag cardinality minus one. -/
noncomputable def width {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) : ℕ :=
  letI : Fintype D.Node := D.nodeFintype
  (Finset.univ.sup fun i : D.Node => (D.bag i).card) - 1

end TreeDecomposition

/-- `G` has a tree decomposition of width at most `k`. -/
def HasTreewidthAtMost {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, D.width ≤ k

/-- The least width of a tree decomposition of `G`.

The fallback makes the definition total. For a finite graph it is unreachable,
because the decomposition with one bag containing every vertex always exists.
-/
noncomputable def treewidth {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  letI := Classical.decPred (HasTreewidthAtMost G)
  letI := Classical.propDecidable (∃ k, HasTreewidthAtMost G k)
  if h : ∃ k, HasTreewidthAtMost G k then Nat.find h else 0

end Lax17.Treewidth
end

-- Lax17.PolynomialGridMinor
section
namespace Lax17.PolynomialGridMinor

universe u

/-- Polynomial excluded-grid theorem with exponent `8 + epsilon`.

The exponent on `(g : ℝ)` is real exponentiation.  The constant is selected
before the graph and grid order, so it depends only on `epsilon`. -/
axiom polynomial_grid_minor_eight_add_epsilon :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 < C ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) {g : ℕ},
            2 ≤ g →
              C * (g : ℝ) ^ ((8 : ℝ) + epsilon) ≤
                  (Lax17.Treewidth.treewidth G : ℝ) →
                Lax17.GridMinor.ContainsGridMinor G g

end Lax17.PolynomialGridMinor
end
