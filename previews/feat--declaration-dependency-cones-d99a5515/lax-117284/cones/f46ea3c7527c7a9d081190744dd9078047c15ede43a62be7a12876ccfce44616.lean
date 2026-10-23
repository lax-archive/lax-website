-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.DeriveFintype

-- Lax271696.GraphEncoding
section
namespace Lax271696.GraphEncoding

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

end Lax271696.GraphEncoding
end

-- Lax117284.BipartiteGraph
section
namespace Lax117284.BipartiteGraph

open Lax271696.GraphEncoding

/-- The left side of a graph on `Fin V` split at `n`: the vertices below `n`. -/
def leftSide (V n : ℕ) : Set (Fin V) := {v | (v : ℕ) < n}

/-- The right side: the vertices from `n` on. -/
def rightSide (V n : ℕ) : Set (Fin V) := {v | n ≤ (v : ℕ)}

/-- **A graph split at `n`**: bipartite with the first `n` vertices on the left and the rest on
the right. -/
def SplitAt {V : ℕ} (G : SimpleGraph (Fin V)) (n : ℕ) : Prop :=
  G.IsBipartiteWith (leftSide V n) (rightSide V n)

/-- **The word `x` presents the bipartite graph `G` on `V` vertices split at `n`**: a compressed
sparse row block encoding `G`, followed by the single entry `n`, with `n ≤ V`. -/
def EncodesBipartite (x : List ℕ) (V : ℕ) (G : SimpleGraph (Fin V)) (n : ℕ) : Prop :=
  ∃ g : List ℕ, x = g ++ [n] ∧ EncodesGraph g V G ∧ n ≤ V ∧ SplitAt G n

end Lax117284.BipartiteGraph
end

-- Lax117284.BipartiteMatching
section
namespace Lax117284
end Lax117284

namespace Lax117284.BipartiteMatching
end Lax117284.BipartiteMatching
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

-- Lax808846.RamComputes
section
namespace Lax808846.RamComputes
end Lax808846.RamComputes
end

-- Lax117284.BipartiteKuhnTime
section
namespace Lax117284.BipartiteKuhnTime
end Lax117284.BipartiteKuhnTime
end

-- Lax759944.BinaryWordEncoding
section
namespace Lax759944
end Lax759944

namespace Lax759944.BinaryWordEncoding
end Lax759944.BinaryWordEncoding

namespace Lax759944.BinaryWordEncoding.Symbol
end Lax759944.BinaryWordEncoding.Symbol

namespace Lax759944.BinaryWordEncoding.Symbol.one
end Lax759944.BinaryWordEncoding.Symbol.one

namespace Lax759944.BinaryWordEncoding.Symbol.separator
end Lax759944.BinaryWordEncoding.Symbol.separator

namespace Lax759944.BinaryWordEncoding.Symbol.zero
end Lax759944.BinaryWordEncoding.Symbol.zero
end

-- Lax759944.RamPolytime
section
namespace Lax759944.RamPolytime
end Lax759944.RamPolytime
end

-- Lax117284.BipartiteDecision
section
namespace Lax117284.BipartiteDecision.WellFormed
end Lax117284.BipartiteDecision.WellFormed

namespace Lax117284.BipartiteDecision

open Lax808846.Ram Lax808846.RamComputes Lax117284.BipartiteGraph Lax117284.BipartiteMatching

open Lax271696.GraphEncoding

/-- The admissible words: encodings of bipartite graphs split at their last entry, fitting the
word length. -/
def Dom (c w : ℕ) : Set (List ℕ) :=
  {x | (∃ (V : ℕ) (G : SimpleGraph (Fin V)) (n : ℕ), EncodesBipartite x V G n) ∧
    c * (x.length + 1) ≤ 2 ^ w}

end Lax117284.BipartiteDecision
end
