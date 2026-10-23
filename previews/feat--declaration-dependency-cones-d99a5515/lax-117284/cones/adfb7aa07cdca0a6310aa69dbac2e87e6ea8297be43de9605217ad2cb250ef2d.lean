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

/-- A **schedule** names, for each day, the clients whose job is executed that day. -/
abbrev Schedule := Fin I.days → Finset (Fin I.clients)

variable {I}

/-- A schedule is **feasible** if the jobs it executes on any one day are pairwise
non-conflicting. -/
def Feasible (σ : I.Schedule) : Prop :=
  ∀ i, (σ i : Set (Fin I.clients)).Pairwise fun j j' => ¬ I.Conflict i j j'

/-- `∑_i Z_{i,j}`, the number of days on which client `j`'s job is executed. -/
def served (σ : I.Schedule) (j : Fin I.clients) : ℕ :=
  (Finset.univ.filter fun i => j ∈ σ i).card

/-- A schedule is **fair** for the parameters `k` if every client `j` is served on at least
`k j` days. -/
def Fair (k : Fin I.clients → ℕ) (σ : I.Schedule) : Prop := ∀ j, k j ≤ served σ j

variable (I)

/-- **The question of `1 | k_j, rep | min_j ∑_i Z_{i,j}`**: is there a feasible schedule
serving every client `j` on at least `k j` days? -/
def HasFairSchedule (k : Fin I.clients → ℕ) : Prop :=
  ∃ σ : I.Schedule, Feasible σ ∧ Fair k σ

end Instance

end Lax117284.Scheduling
end

-- Lax228581.Treewidth
section
namespace Lax228581.Treewidth

/-- A tree decomposition of a simple graph: a finite tree of nodes with a bag
of graph vertices at each node, such that the bags cover every vertex and
every edge, and the nodes whose bags contain any fixed vertex induce a
connected subgraph of the tree. -/
structure TreeDecomposition {V : Type} (G : SimpleGraph V) where
  /-- The node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree is finite. -/
  [nodeFintype : Fintype Node]
  /-- The graph on the decomposition nodes. -/
  tree : SimpleGraph Node
  /-- The node graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag assigned to each decomposition node. -/
  bag : Node → Finset V
  /-- Every graph vertex appears in at least one bag. -/
  vertex_mem_bag : ∀ v : V, ∃ i : Node, v ∈ bag i
  /-- Every graph edge has both endpoints together in at least one bag. -/
  edge_mem_bag : ∀ ⦃u v : V⦄, G.Adj u v → ∃ i : Node, u ∈ bag i ∧ v ∈ bag i
  /-- For each graph vertex, the nodes whose bags contain it induce a
  connected subgraph of the tree. -/
  bag_indices_connected :
    ∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected

/-- `G` has a tree decomposition all of whose bags have at most `w + 1`
vertices. -/
def HasTreewidthAtMost {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, ∀ i, (D.bag i).card ≤ w + 1

/-- The treewidth of a finite simple graph: the least `w` such that the
graph has a tree decomposition with bags of at most `w + 1` vertices. -/
noncomputable def treewidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {w | HasTreewidthAtMost G w}

end Lax228581.Treewidth
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

/-- The treewidth `τ` of the overall conflict graph of `I`. -/
noncomputable def treewidth : ℕ := Lax228581.Treewidth.treewidth (overallGraph I)

end Lax117284.ConflictGraph
end

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}

end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair

namespace Lax434930.Certificates

open PolynomialTime

/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y

end Lax434930.Certificates
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime

open PolynomialTime Certificates

/-- Languages with polynomially bounded, polynomial-time verifiable certificates. -/
def NP : Set Language :=
  {A | ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V}

end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075.Reductions

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

def ManyOne (A B : Language) : Prop :=
  ∃ f : Word → Word, Nonempty (Turing.TM2ComputableInPolyTime id id f) ∧
    ∀ x, x ∈ A ↔ f x ∈ B

end Lax429075.Reductions
end

-- Lax117284.Problems
section
namespace Lax117284.Problems

open Lax117284.Scheduling Lax434930.PolynomialTime

open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- An instance as a binary word: the number of clients, the number of days, then the
processing time and the due date of every job. -/
def encodeInstance (I : Instance) : Word :=
  encodeNat I.clients ++ encodeNat I.days ++
    (List.finRange I.days).flatMap fun i =>
      (List.finRange I.clients).flatMap fun j => encodeNat (I.p i j) ++ encodeNat (I.d i j)

/-- An instance of `1 | k_j, rep | min_j ∑_i Z_{i,j}`: an instance followed by one
fairness parameter per client. -/
def encodePerClient (I : Instance) (k : Fin I.clients → ℕ) : Word :=
  encodeInstance I ++ (List.finRange I.clients).flatMap fun j => encodeNat (k j)

/-- **`1 | k_j, rep | min_j ∑_i Z_{i,j}` on the class `C`**, as a language. -/
def PerClient (C : (I : Instance) → (Fin I.clients → ℕ) → Prop) : Language :=
  {w | ∃ (I : Instance) (k : Fin I.clients → ℕ),
    encodePerClient I k = w ∧ C I k ∧ I.HasFairSchedule k}

/-- A language is **NP-hard** if every language in NP reduces to it in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ A : Language, A ∈ NP → ManyOne A L

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

end Instance

end Lax117284.MulticolouredIndepSet
end

-- Lax117284.Lemma14
section
namespace Lax117284.Lemma14

open Lax117284.Problems Lax117284.MulticolouredIndepSet

open Lax434930.PolynomialTime Lax429075.Reductions

variable (G : Instance)

/-- **Lemma 14.** The per-client problem is NP-hard on the instances whose overall conflict
graph has treewidth at most `4`. -/
axiom perClient_npHard :
    NPHard (PerClient fun I k => ConflictGraph.treewidth I ≤ 4 ∧ ∀ j, k j ≤ I.days)

end Lax117284.Lemma14
end
