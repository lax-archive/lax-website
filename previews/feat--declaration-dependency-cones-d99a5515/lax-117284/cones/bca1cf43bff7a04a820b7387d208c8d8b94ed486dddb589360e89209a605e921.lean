-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

-- Lax271696.GraphEncoding
section
namespace Lax271696.GraphEncoding.EncodesGraph
end Lax271696.GraphEncoding.EncodesGraph

namespace Lax271696.GraphEncoding

/-- The number of vertices declared by a word: its first entry. -/
def vertexCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The `i`-th offset of a word: the `n+1` offsets follow the two
header entries. -/
def offset (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + i) 0

/-- The `j`-th entry of the target array of a word, which follows the
header and the offsets. -/
def target (x : List ℕ) (j : ℕ) : ℕ := x.getD (3 + vertexCount x + j) 0

end Lax271696.GraphEncoding
end

-- Lax117284.BipartiteGraph
section
namespace Lax117284.BipartiteGraph

open Lax271696.GraphEncoding

/-- Vertex `u` lists vertex `v` in its block. -/
def Lists (x : List ℕ) (u v : ℕ) : Prop :=
  ∃ j, offset x u ≤ j ∧ j < offset x (u + 1) ∧ target x j = v

/-- The graph a word denotes: two distinct vertices are adjacent when either lists the other. -/
def wordGraph (x : List ℕ) : SimpleGraph (Fin (vertexCount x)) :=
  SimpleGraph.fromRel fun u v : Fin (vertexCount x) => Lists x u v

end Lax117284.BipartiteGraph
end
