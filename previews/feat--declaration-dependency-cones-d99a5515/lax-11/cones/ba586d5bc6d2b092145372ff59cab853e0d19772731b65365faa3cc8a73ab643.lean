-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax11.CliqueExpr
section
namespace Lax11.CliqueExpr

variable {n k : ℕ}

/-- A `k`-expression over the vertex names `Fin n`: a single labelled
vertex, disjoint union, edge addition between two label classes, or
relabelling one class into another. -/
inductive Expr (n k : ℕ) : Type
  /-- The vertex `v`, carrying label `l`. -/
  | leaf (v : Fin n) (l : Fin k)
  /-- Disjoint union `⊕`. -/
  | union (e₁ e₂ : Expr n k)
  /-- `η i j`: join every vertex of class `i` to every vertex of class `j`. -/
  | addEdges (i j : Fin k) (e : Expr n k)
  /-- `ρ i j`: move class `i` into class `j`. -/
  | relabel (i j : Fin k) (e : Expr n k)

/-- The vertex names created by the leaves, in order. -/
def leafIds : Expr n k → List (Fin n)
  | .leaf v _ => [v]
  | .union e₁ e₂ => leafIds e₁ ++ leafIds e₂
  | .addEdges _ _ e => leafIds e
  | .relabel _ _ e => leafIds e

/-- The vertex set of an expression. -/
def verts : Expr n k → Finset (Fin n)
  | .leaf v _ => {v}
  | .union e₁ e₂ => verts e₁ ∪ verts e₂
  | .addEdges _ _ e => verts e
  | .relabel _ _ e => verts e

/-- The label classes of an expression: `cls e i` is the set of vertices
of `e` currently carrying label `i`. -/
def cls : Expr n k → Fin k → Finset (Fin n)
  | .leaf v l, i => if i = l then {v} else ∅
  | .union e₁ e₂, i => cls e₁ i ∪ cls e₂ i
  | .addEdges _ _ e, i => cls e i
  | .relabel i j e, t => if t = j then cls e i ∪ cls e j else if t = i then ∅ else cls e t

/-- The graph an expression evaluates to. -/
def graph : Expr n k → SimpleGraph (Fin n)
  | .leaf _ _ => ⊥
  | .union e₁ e₂ => graph e₁ ⊔ graph e₂
  | .addEdges i j e => graph e ⊔ SimpleGraph.fromRel fun u v => u ∈ cls e i ∧ v ∈ cls e j
  | .relabel _ _ e => graph e

/-- Well-formedness of the operations: `addEdges` joins two *different*
classes, the standard restriction on `η`. -/
def opsOk : Expr n k → Bool
  | .leaf _ _ => true
  | .union e₁ e₂ => opsOk e₁ && opsOk e₂
  | .addEdges i j e => (i != j) && opsOk e
  | .relabel _ _ e => opsOk e

/-- A valid expression: the leaves create pairwise distinct vertices —
which is what makes the two sides of every `⊕` disjoint — and the
operations are well formed. -/
structure Valid (e : Expr n k) : Prop where
  /-- No vertex name is created twice. -/
  nodup : (leafIds e).Nodup
  /-- Every `addEdges` joins two different classes. -/
  ops : opsOk e = true

/-- A `k`-expression *for* `G`: valid, and at the root it has created
every vertex and exactly the edges of `G`. -/
structure ValidFor (e : Expr n k) (G : SimpleGraph (Fin n)) : Prop extends Valid e where
  /-- The root creates every vertex. -/
  verts_eq : verts e = Finset.univ
  /-- The root evaluates to `G`. -/
  graph_eq : graph e = G

/-- The operation performed at a node of a `k`-expression. -/
inductive Op (k : ℕ) where
  /-- Disjoint union. -/
  | union
  /-- Create a vertex with label `l`. -/
  | leaf (l : Fin k)
  /-- `η i j`: join class `i` to class `j`. -/
  | eta (i j : Fin k)
  /-- `ρ i j`: move class `i` into class `j`. -/
  | rho (i j : Fin k)
  deriving DecidableEq

/-- The number naming an operation. The blocks are `union` (one code),
the leaves (`k` codes), the joins and the relabels (`k²` codes each,
the pair `(i, j)` read in base `k`). -/
def Op.code : Op k → ℕ
  | .union => 0
  | .leaf l => 1 + (l : ℕ)
  | .eta i j => 1 + k + ((i : ℕ) * k + (j : ℕ))
  | .rho i j => 1 + k + k * k + ((i : ℕ) * k + (j : ℕ))

/-- The size of the operation alphabet. -/
def opCard (k : ℕ) : ℕ := 1 + k + 2 * (k * k)

end Lax11.CliqueExpr
end

-- Lax11.GraphEncoding
section
namespace Lax11.GraphEncoding

/-- The number of vertices declared by a word: its first entry. -/
def vertexCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of edges declared by a word: its second entry. -/
def edgeCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The `i`-th offset of a word: the `n+1` offsets follow the two
header entries. -/
def offset (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + i) 0

/-- The `j`-th entry of the target array of a word, which follows the
header and the offsets. -/
def target (x : List ℕ) (j : ℕ) : ℕ := x.getD (3 + vertexCount x + j) 0

/-- The word `x` is a compressed sparse row encoding of the graph `G`
on `n` vertices. -/
structure EncodesGraph (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) :
    Prop where
  /-- The word declares `n` vertices. -/
  vertexCount_eq : vertexCount x = n
  /-- The word consists of the two header entries, the `n+1` offsets,
  and a target array of length twice the declared number of edges. -/
  length_eq : x.length = 3 + n + 2 * edgeCount x
  /-- The block of the first vertex begins at the start of the target
  array. -/
  offset_zero : offset x 0 = 0
  /-- The block of the last vertex ends at the end of the target
  array. -/
  offset_last : offset x n = 2 * edgeCount x
  /-- The offsets are nondecreasing, so they cut the target array into
  one block per vertex. -/
  offset_mono : ∀ i < n, offset x i ≤ offset x (i + 1)
  /-- Every entry of the target array is a vertex. -/
  target_lt : ∀ j < 2 * edgeCount x, target x j < n
  /-- The block of a vertex lists exactly its neighbors. -/
  adj_iff : ∀ u v : Fin n, G.Adj u v ↔
    ∃ j, offset x u ≤ j ∧ j < offset x (u + 1) ∧ target x j = v

end Lax11.GraphEncoding
end

-- Lax11.InstanceEncoding
section
namespace Lax11.InstanceEncoding

open Lax11.GraphEncoding Lax11.CliqueExpr

/-- The number of nodes declared by an expression block: its first
entry. -/
def nodeCount (t : List ℕ) : ℕ := t.getD 0 0

/-- The parent of node `i`: the parents follow the header entry. -/
def parent (t : List ℕ) (i : ℕ) : ℕ := t.getD (1 + i) 0

/-- The operation performed at node `i`, as a number: the operations
follow the parents. -/
def opCode (t : List ℕ) (i : ℕ) : ℕ := t.getD (1 + nodeCount t + i) 0

/-- The vertex name created at node `i`, meaningful when the operation
there creates a vertex: the names follow the operations. -/
def vertexName (t : List ℕ) (i : ℕ) : ℕ := t.getD (1 + 2 * nodeCount t + i) 0

/-- The children of node `i`: the earlier nodes whose parent is `i`,
in increasing order. -/
def children (par : ℕ → ℕ) (i : ℕ) : List ℕ :=
  (List.range i).filter (fun c => par c == i)

/-- The word `t` is an expression block for a tree whose operations are
operations of `k`-expressions. The number of nodes is the block's own
first entry, so it is read off `t` rather than quantified over. -/
structure EncodesExprTree (t : List ℕ) (k : ℕ) : Prop where
  /-- There is at least one node: an expression has a root. -/
  pos : 1 ≤ nodeCount t
  /-- The block consists of the header entry and three arrays of one
  number per node. -/
  length_eq : t.length = 1 + 3 * nodeCount t
  /-- Every node but the last has a parent, which is a later node — so
  children are numbered before their parents and the root is the last
  node. -/
  parent_gt : ∀ i, i + 1 < nodeCount t → i < parent t i ∧ parent t i < nodeCount t
  /-- Every operation entry is the number of an operation. -/
  opCode_lt : ∀ i < nodeCount t, opCode t i < opCard k

/-- The node `i` of the tree given by the three arrays is the
expression `e`: the operation number at `i` is the one of `e`'s
outermost operation, the vertex name at `i` is the one `e` creates if
`e` is a leaf, and the children of `i` — which are listed in increasing
order — are the nodes of `e`'s immediate subexpressions, the left one
first. -/
def EncodesExpr {n k : ℕ} (par lab ids : ℕ → ℕ) : ℕ → Expr n k → Prop
  | i, .leaf v l => children par i = [] ∧ lab i = (Op.leaf l).code ∧ ids i = (v : ℕ)
  | i, .union e₁ e₂ => ∃ c₁ c₂, children par i = [c₁, c₂] ∧
      lab i = (Op.union : Op k).code ∧
      EncodesExpr par lab ids c₁ e₁ ∧ EncodesExpr par lab ids c₂ e₂
  | i, .addEdges a b e => ∃ c, children par i = [c] ∧
      lab i = (Op.eta a b).code ∧ EncodesExpr par lab ids c e
  | i, .relabel a b e => ∃ c, children par i = [c] ∧
      lab i = (Op.rho a b).code ∧ EncodesExpr par lab ids c e

/-- The word `x` presents the graph `G` on `n` vertices together with a
`k`-expression for it: a compressed sparse row block encoding `G`,
followed by an expression block whose arrays describe a valid
`k`-expression, rooted at its last node, that evaluates to `G`. This is
the instance format of a model checking problem on graphs of bounded
cliquewidth. -/
def EncodesModelCheckingInstance (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n))
    (k : ℕ) : Prop :=
  ∃ (g t : List ℕ) (e : Expr n k),
    x = g ++ t ∧ EncodesGraph g n G ∧ EncodesExprTree t k ∧
      EncodesExpr (parent t) (opCode t) (vertexName t) (nodeCount t - 1) e ∧ ValidFor e G

end Lax11.InstanceEncoding
end
