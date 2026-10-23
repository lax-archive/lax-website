-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Interval.Set.Basic

-- Lax117284.Scheduling
section
namespace Lax117284.Scheduling

/-- An instance of fair repetitive interval scheduling: `clients` clients each submitting
one job on each of `days` days, where client `j`'s job on day `i` has processing time
`p i j` and due date `d i j`. A job takes some time and does not start before time `0`. -/
structure Instance where
  /-- The number `n` of clients. -/
  clients : ℕ
  /-- The number `m` of days. -/
  days : ℕ
  /-- The processing time `p i j` of client `j`'s job on day `i`. -/
  p : Fin days → Fin clients → ℕ
  /-- The due date `d i j` of client `j`'s job on day `i`. -/
  d : Fin days → Fin clients → ℕ
  /-- Every job takes some time. -/
  p_pos : ∀ i j, 0 < p i j
  /-- No job starts before time `0`. -/
  p_le_d : ∀ i j, p i j ≤ d i j

namespace Instance

variable (I : Instance)

/-- The interval `(d i j - p i j, d i j]` occupied by client `j`'s job on day `i`: the job
is completed exactly at its due date. -/
def job (i : Fin I.days) (j : Fin I.clients) : Set ℕ :=
  Set.Ioc (I.d i j - I.p i j) (I.d i j)

/-- Clients `j` and `j'` **conflict on day `i`**: their day-`i` jobs share a time point, so
the machine of that day can execute at most one of them. -/
def Conflict (i : Fin I.days) (j j' : Fin I.clients) : Prop :=
  (I.job i j ∩ I.job i j').Nonempty

variable {I}

variable (I)

end Instance

end Lax117284.Scheduling
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

open Lax117284.Scheduling

/-- Conflict is a symmetric relation: the two jobs share a time point either way. -/
theorem conflict_symm {I : Instance} {i : Fin I.days} {j j' : Fin I.clients}
    (h : I.Conflict i j j') : I.Conflict i j' j :=
  let ⟨t, ht⟩ := h; ⟨t, ht.2, ht.1⟩

variable (I : Instance)

/-- **The overall conflict graph** of `I`: two distinct clients are adjacent when their
jobs conflict on some day. -/
def overallGraph : SimpleGraph (Fin I.clients) where
  Adj j j' := j ≠ j' ∧ ∃ i, I.Conflict i j j'
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ => conflict_symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end Lax117284.ConflictGraph
end

-- Lax117284.InstanceEncoding
section
namespace Lax117284.InstanceEncoding
end Lax117284.InstanceEncoding

namespace Lax117284.InstanceEncoding.EncodesInstance
end Lax117284.InstanceEncoding.EncodesInstance
end

-- Lax808846.Ram
section
namespace Lax808846
end Lax808846

namespace Lax808846.Ram
end Lax808846.Ram

namespace Lax808846.Ram.Instr
end Lax808846.Ram.Instr

namespace Lax808846.Ram.State
end Lax808846.Ram.State

namespace Lax808846.Ram.run
end Lax808846.Ram.run

namespace Lax808846.Ram.Instr.add
end Lax808846.Ram.Instr.add

namespace Lax808846.Ram.Instr.and
end Lax808846.Ram.Instr.and

namespace Lax808846.Ram.Instr.div
end Lax808846.Ram.Instr.div

namespace Lax808846.Ram.Instr.effect
end Lax808846.Ram.Instr.effect

namespace Lax808846.Ram.Instr.halt
end Lax808846.Ram.Instr.halt

namespace Lax808846.Ram.Instr.inputLength
end Lax808846.Ram.Instr.inputLength

namespace Lax808846.Ram.Instr.inputLoad
end Lax808846.Ram.Instr.inputLoad

namespace Lax808846.Ram.Instr.jeof
end Lax808846.Ram.Instr.jeof

namespace Lax808846.Ram.Instr.jump
end Lax808846.Ram.Instr.jump

namespace Lax808846.Ram.Instr.jzero
end Lax808846.Ram.Instr.jzero

namespace Lax808846.Ram.Instr.load
end Lax808846.Ram.Instr.load

namespace Lax808846.Ram.Instr.mul
end Lax808846.Ram.Instr.mul

namespace Lax808846.Ram.Instr.not
end Lax808846.Ram.Instr.not

namespace Lax808846.Ram.Instr.read
end Lax808846.Ram.Instr.read

namespace Lax808846.Ram.Instr.set
end Lax808846.Ram.Instr.set

namespace Lax808846.Ram.Instr.shiftl
end Lax808846.Ram.Instr.shiftl

namespace Lax808846.Ram.Instr.store
end Lax808846.Ram.Instr.store

namespace Lax808846.Ram.Instr.sub
end Lax808846.Ram.Instr.sub

namespace Lax808846.Ram.Instr.write
end Lax808846.Ram.Instr.write
end

-- Lax117284.Bodlaender
section
namespace Lax117284.Bodlaender.EncodesGraph
end Lax117284.Bodlaender.EncodesGraph

namespace Lax117284.Bodlaender

open Lax808846.Ram Lax117284.Scheduling Lax117284.ConflictGraph

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

/-- **`D` is the word of a nice tree decomposition of the overall conflict graph of `I` of width
at most `w`.** -/
structure NiceDecomposition (I : Instance) (w : ℕ) (D : List ℕ) : Prop where
  /-- The word is `N` followed by three numbers for each of the `N` nodes. -/
  length_eq : D.length = 1 + 3 * nodeCount D
  /-- There is a node. -/
  nonempty : 0 < nodeCount D
  /-- Every node is a leaf, or an introduce node over the node before it whose vertex is not in
  that node's bag, or a forget node over the node before it whose vertex is in that node's bag,
  or a join node whose two children, the node before it and an earlier node, have its bag. -/
  shape : ∀ i, i < nodeCount D →
    kind D i = 0 ∨
    (0 < i ∧ kind D i = 1 ∧ vertex D i < I.clients ∧
      ∀ h : vertex D i < I.clients, (⟨vertex D i, h⟩ : Fin I.clients) ∉ bagAt I.clients D (i - 1)) ∨
    (0 < i ∧ kind D i = 2 ∧ vertex D i < I.clients ∧
      ∀ h : vertex D i < I.clients, (⟨vertex D i, h⟩ : Fin I.clients) ∈ bagAt I.clients D (i - 1)) ∨
    (0 < i ∧ kind D i = 3 ∧ other D i + 1 < i ∧
      bagAt I.clients D (other D i) = bagAt I.clients D (i - 1))
  /-- Every node other than the last has exactly one parent. -/
  parent : ∀ c, c + 1 < nodeCount D → ∃! p, IsChild D c p
  /-- The nodes form a tree. -/
  isTree : (treeGraph D).IsTree
  /-- Every client is in a bag. -/
  covers : ∀ v : Fin I.clients, ∃ i, i < nodeCount D ∧ v ∈ bagAt I.clients D i
  /-- Every two clients whose jobs conflict on some day are in a bag together. -/
  edges : ∀ u v : Fin I.clients, (overallGraph I).Adj u v →
    ∃ i, i < nodeCount D ∧ u ∈ bagAt I.clients D i ∧ v ∈ bagAt I.clients D i
  /-- The nodes whose bags contain a fixed client form a connected subtree. -/
  connected : ∀ v : Fin I.clients,
    ((treeGraph D).induce {i : Fin (nodeCount D) | v ∈ bagAt I.clients D i}).Connected
  /-- Every bag has at most `w + 1` clients. -/
  width : ∀ i, i < nodeCount D → (bagAt I.clients D i).card ≤ w + 1

end Lax117284.Bodlaender
end
