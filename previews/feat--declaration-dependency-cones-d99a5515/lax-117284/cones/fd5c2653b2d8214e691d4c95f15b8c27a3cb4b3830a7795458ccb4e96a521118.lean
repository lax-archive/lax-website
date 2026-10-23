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
namespace Lax808846.Ram

/-- An instruction. Every number naming a cell is read, except that
the first one names the destination for instructions that write a cell,
and the cell holding the destination address for `store`. `set` carries
a literal value; `jump`, `jzero`, and `jeof` carry program labels,
which are not data-memory addresses. -/
inductive Instr
  /-- Set cell `a` to the literal `n`. -/
  | set (a n : ℕ)
  /-- Set cell `a` to the contents of the cell whose address cell `b`
  holds. -/
  | load (a b : ℕ)
  /-- Set the cell whose address cell `a` holds to the contents of cell
  `b`. -/
  | store (a b : ℕ)
  /-- Set cell `a` to the sum of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | add (a b c : ℕ)
  /-- Set cell `a` to the difference of cells `b` and `c`, truncated at
  zero rather than wrapping around. -/
  | sub (a b c : ℕ)
  /-- Set cell `a` to the product of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | mul (a b c : ℕ)
  /-- Set cell `a` to the quotient of cells `b` and `c`, rounding
  towards zero; division by zero yields zero. -/
  | div (a b c : ℕ)
  /-- Set cell `a` to the bitwise conjunction of cells `b` and `c`. -/
  | and (a b c : ℕ)
  /-- Set cell `a` to cell `b` shifted left by the number of bits cell
  `c` holds, wrapping around modulo `2 ^ w`; a shift by `w` or more
  yields zero. -/
  | shiftl (a b c : ℕ)
  /-- Set cell `a` to the bitwise complement `2 ^ w - 1 - m[b]` of cell
  `b` within the word length. -/
  | not (a b : ℕ)
  /-- Continue at instruction `l`. -/
  | jump (l : ℕ)
  /-- Continue at instruction `l` if cell `a` is zero. -/
  | jzero (a l : ℕ)
  /-- Continue at instruction `l` exactly when the remaining input tape
  is empty. This test does not consume input. -/
  | jeof (l : ℕ)
  /-- Write the original input length, reduced to a word, into cell `a`. -/
  | inputLength (a : ℕ)
  /-- Read original input at the word index in cell `b` into cell `a`,
  returning zero outside the input. Read the index before writing `a`,
  even when the two cell addresses coincide. Do not consume input. -/
  | inputLoad (a b : ℕ)
  /-- Halt. -/
  | halt
  /-- Read the next number of the input tape into cell `a`, or halt if
  the tape is exhausted. -/
  | read (a : ℕ)
  /-- Append the contents of cell `a` to the output tape. -/
  | write (a : ℕ)

/-- A program: a finite sequence of instructions, numbered from `0`. -/
abbrev Program : Type := List Instr

/-- A machine state: the program counter, the contents of every memory
cell, the immutable original input array, the remaining sequential input
tape, and the output tape written so far. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The contents of the memory cells; only the cells with number below
  `2 ^ w` are ever addressed. -/
  mem : ℕ → ℕ
  /-- The original read-only input, unchanged by every instruction. -/
  input : List ℕ
  /-- The numbers still to be read from the input tape. -/
  inp : List ℕ
  /-- The numbers written to the output tape so far. -/
  out : List ℕ

/-- The memory `m` with cell `a` set to `v`, at word length `w`: the
address and the value written are both taken modulo `2 ^ w`. -/
def setCell (w : ℕ) (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun b => if b = a % 2 ^ w then v % 2 ^ w else m b

/-- The effect of one instruction on the state at word length `w`, or
`none` if it halts the machine, which a `halt` instruction and a read
from an exhausted input tape do. Data values, input indices, and
data-memory addresses are reduced modulo `2 ^ w`; program labels and
the counter are not. -/
def Instr.effect (w : ℕ) : Instr → State → Option State
  | set a n, s => some { s with pc := s.pc + 1, mem := setCell w s.mem a n }
  | load a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (s.mem (b % 2 ^ w) % 2 ^ w)) }
  | store a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem (s.mem (a % 2 ^ w)) (s.mem (b % 2 ^ w)) }
  | add a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) + s.mem (c % 2 ^ w)) }
  | sub a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) - s.mem (c % 2 ^ w)) }
  | mul a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * s.mem (c % 2 ^ w)) }
  | div a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) / s.mem (c % 2 ^ w)) }
  | and a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (Nat.land (s.mem (b % 2 ^ w)) (s.mem (c % 2 ^ w))) }
  | shiftl a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * 2 ^ s.mem (c % 2 ^ w)) }
  | not a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (2 ^ w - 1 - s.mem (b % 2 ^ w)) }
  | jump l, s => some { s with pc := l }
  | jzero a l, s => some { s with pc := if s.mem (a % 2 ^ w) = 0 then l else s.pc + 1 }
  | jeof l, s => some { s with pc := if s.inp.isEmpty then l else s.pc + 1 }
  | inputLength a, s =>
      some { s with pc := s.pc + 1, mem := setCell w s.mem a s.input.length }
  | inputLoad a b, s =>
      some { s with
        pc := s.pc + 1
        mem := setCell w s.mem a (s.input[s.mem (b % 2 ^ w) % 2 ^ w]?.getD 0) }
  | halt, _ => none
  | read a, s =>
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := s.inp.tail }
  | write a, s =>
      some { s with pc := s.pc + 1, out := s.out ++ [s.mem (a % 2 ^ w) % 2 ^ w] }

/-- One step of the machine at word length `w`: fetch the instruction
the program counter points at and execute it. The result is `none` if
the machine has halted, which also happens when the program counter has
run past the program. -/
def step (w : ℕ) (p : Program) (s : State) : Option State :=
  p[s.pc]?.bind fun i => i.effect w s

/-- The state after `t` successful transitions at word length `w`, or
`none` if one of those transitions terminates. This auxiliary count does
not include a fetched terminal instruction; `RunsTo` charges that too. -/
def run (w : ℕ) (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

/-- The initial state on input `x`: program counter zero, all memory
cells zero, the original input array and its sequential tape both `x`,
and the output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  mem := fun _ => 0
  input := x
  inp := x
  out := []

/-- Cost of termination at `s`, when `step w p s = none`: a fetched
terminal instruction costs one, while an out-of-range program counter
costs zero because there is no instruction to execute. -/
def terminalCost (p : Program) (s : State) : ℕ :=
  if s.pc < p.length then 1 else 0

/-- Started on input `x` at word length `w`, the machine executes
exactly `t` instructions and then halts, having written the word `y` to
its output tape. -/
def RunsTo (w : ℕ) (p : Program) (x y : List ℕ) (t : ℕ) : Prop :=
  ∃ (k : ℕ) (s : State), run w p k (initState x) = some s ∧
    step w p s = none ∧ s.out = y ∧ t = k + terminalCost p s

end Lax808846.Ram
end

-- Lax117284.Bodlaender
section
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

open Classical in
/-- **`g` is the word of the overall conflict graph of `I`**: the number of clients, then the
adjacency matrix row by row. -/
structure EncodesGraph (g : List ℕ) (I : Instance) : Prop where
  /-- The word is the count followed by the matrix. -/
  length_eq : g.length = 1 + I.clients * I.clients
  /-- The first entry is the number of clients. -/
  head_eq : g.getD 0 0 = I.clients
  /-- The entry of the row `u` and column `v` is `1` when the two clients are adjacent and `0`
  otherwise. -/
  adj_eq : ∀ u v : Fin I.clients,
    g.getD (1 + u.val * I.clients + v.val) 0 = if (overallGraph I).Adj u v then 1 else 0

/-- **Bodlaender's theorem with Kloks' niceness, for the overall conflict graph of an instance
given as a word.** One program and one constant serve every word length `W`, every graph and every
bound `w`, provided the word — the graph followed by `w` — fits with room for
`c * 2 ^ (c * w ^ 3)` times a polynomial in its length. On such a word the program halts within
`c * 2 ^ (c * w ^ 3) * (|g| + 2) ^ c` instructions, writing `[0]` if the graph has no tree
decomposition of width at most `w`, and `1` followed by the word of a nice tree decomposition of
width at most `w` otherwise. -/
axiom niceDecomposition_computable :
    ∃ (prog : Program) (c : ℕ), ∀ (W w : ℕ) (g : List ℕ) (I : Instance),
      EncodesGraph g I →
      (∀ v ∈ g ++ [w], c * 2 ^ (c * w ^ 3) * ((g ++ [w]).length + v + 1) ^ c ≤ 2 ^ W) →
      ∃ (out : List ℕ) (t : ℕ), t ≤ c * 2 ^ (c * w ^ 3) * (g.length + 2) ^ c ∧
        RunsTo W prog (g ++ [w]) out t ∧
        (out = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost (overallGraph I) w ∨
          ∃ D, out = 1 :: D ∧ NiceDecomposition I w D)

end Lax117284.Bodlaender
end
