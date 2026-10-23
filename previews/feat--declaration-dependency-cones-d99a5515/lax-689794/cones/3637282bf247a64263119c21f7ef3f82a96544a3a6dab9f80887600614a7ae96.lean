-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Lattice

-- Lax228581.Treewidth
section
namespace Lax228581
end Lax228581

namespace Lax228581.Treewidth
end Lax228581.Treewidth

namespace Lax228581.Treewidth.TreeDecomposition
end Lax228581.Treewidth.TreeDecomposition
end

-- Lax689794.GraphWords
section
namespace Lax689794.GraphWords.EncodesGraph
end Lax689794.GraphWords.EncodesGraph

namespace Lax689794.GraphWords

open Lax228581.Treewidth

/-- The number of nodes of the decomposition word `D`: its first entry. -/
def nodeCount (D : List ℕ) : ℕ := D.getD 0 0

/-- The kind of node `i`: `0` leaf, `1` introduce, `2` forget, `3` join. -/
def kind (D : List ℕ) (i : ℕ) : ℕ := D.getD (1 + 3 * i) 0

/-- The vertex of node `i`, for an introduce or a forget node. -/
def vertex (D : List ℕ) (i : ℕ) : ℕ := D.getD (2 + 3 * i) 0

/-- The second child of node `i`, for a join node. -/
def other (D : List ℕ) (i : ℕ) : ℕ := D.getD (3 + 3 * i) 0

/-- The bag of node `i` among the vertices `0 … n - 1`, from the leaves up: the empty bag at a
leaf, the child's bag plus the vertex at an introduce node, minus it at a forget node, and the
child's bag at a join node. The first child of node `i + 1` is node `i`. -/
def bagAt (n : ℕ) (D : List ℕ) : ℕ → Finset (Fin n)
  | 0 => ∅
  | i + 1 =>
      if kind D (i + 1) = 1 then
        if h : vertex D (i + 1) < n then insert ⟨vertex D (i + 1), h⟩ (bagAt n D i)
        else bagAt n D i
      else if kind D (i + 1) = 2 then
        if h : vertex D (i + 1) < n then (bagAt n D i).erase ⟨vertex D (i + 1), h⟩
        else bagAt n D i
      else if kind D (i + 1) = 3 then bagAt n D i
      else ∅

/-- Node `c` is a child of node `p`. -/
def IsChild (D : List ℕ) (c p : ℕ) : Prop :=
  p < nodeCount D ∧
    ((kind D p = 1 ∨ kind D p = 2) ∧ c + 1 = p ∨ kind D p = 3 ∧ (c + 1 = p ∨ c = other D p))

/-- The graph on the nodes `0 … N - 1` whose edges join a node to its children. -/
def treeGraph (D : List ℕ) : SimpleGraph (Fin (nodeCount D)) where
  Adj a b := a ≠ b ∧ (IsChild D a.val b.val ∨ IsChild D b.val a.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **`D` is the word of a nice tree decomposition of `G` of width at most `w`.** -/
structure NiceDecomposition {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) (D : List ℕ) : Prop where
  /-- The word is `N` followed by three numbers for each of the `N` nodes. -/
  length_eq : D.length = 1 + 3 * nodeCount D
  /-- There is a node. -/
  nonempty : 0 < nodeCount D
  /-- Every node is a leaf, or an introduce node over the node before it whose vertex is not in
  that node's bag, or a forget node over the node before it whose vertex is in that node's bag,
  or a join node whose two children, the node before it and an earlier node, have its bag. -/
  shape : ∀ i, i < nodeCount D →
    kind D i = 0 ∨
    (0 < i ∧ kind D i = 1 ∧ vertex D i < n ∧
      ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∉ bagAt n D (i - 1)) ∨
    (0 < i ∧ kind D i = 2 ∧ vertex D i < n ∧
      ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∈ bagAt n D (i - 1)) ∨
    (0 < i ∧ kind D i = 3 ∧ other D i + 1 < i ∧
      bagAt n D (other D i) = bagAt n D (i - 1))
  /-- Every node other than the last has exactly one parent. -/
  parent : ∀ c, c + 1 < nodeCount D → ∃! p, IsChild D c p
  /-- The nodes form a tree. -/
  isTree : (treeGraph D).IsTree
  /-- Every vertex is in a bag. -/
  covers : ∀ v : Fin n, ∃ i, i < nodeCount D ∧ v ∈ bagAt n D i
  /-- Every two adjacent vertices are in a bag together. -/
  edges : ∀ u v : Fin n, G.Adj u v →
    ∃ i, i < nodeCount D ∧ u ∈ bagAt n D i ∧ v ∈ bagAt n D i
  /-- The nodes whose bags contain a fixed vertex form a connected subtree. -/
  connected : ∀ v : Fin n,
    ((treeGraph D).induce {i : Fin (nodeCount D) | v ∈ bagAt n D i}).Connected
  /-- Every bag has at most `w + 1` vertices. -/
  width : ∀ i, i < nodeCount D → (bagAt n D i).card ≤ w + 1

end Lax689794.GraphWords
end
