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
namespace Lax271696.GraphEncoding.EncodesGraph
end Lax271696.GraphEncoding.EncodesGraph

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

end Lax271696.GraphEncoding
end

-- Lax117284.BipartiteGraph
section
namespace Lax117284.BipartiteGraph

open Lax271696.GraphEncoding

/-- The number of left vertices a word declares: its last entry. -/
def leftCount (x : List ℕ) : ℕ := x.getLastD 0

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
namespace Lax117284.BipartiteDecision

open Lax808846.Ram Lax808846.RamComputes Lax117284.BipartiteGraph Lax117284.BipartiteMatching

open Lax271696.GraphEncoding

/-- **A well-formed bipartite word**: at least as many vertices as left vertices, the length of
a compressed sparse row block plus the split, offsets starting at `0`, ending at twice the edge
count and nondecreasing, every target a vertex, and every listed edge crossing the split. -/
structure WellFormed (x : List ℕ) : Prop where
  /-- The left vertices are among the vertices. -/
  left_le : leftCount x ≤ vertexCount x
  /-- The compressed sparse row block, then the split. -/
  length_eq : x.length = 4 + vertexCount x + 2 * edgeCount x
  /-- The first offset is `0`. -/
  offset_zero : offset x 0 = 0
  /-- The last offset is twice the edge count. -/
  offset_last : offset x (vertexCount x) = 2 * edgeCount x
  /-- The offsets are nondecreasing. -/
  offset_mono : ∀ i < vertexCount x, offset x i ≤ offset x (i + 1)
  /-- Every target is a vertex. -/
  target_lt : ∀ j < 2 * edgeCount x, target x j < vertexCount x
  /-- Every listed edge crosses the split. -/
  crosses : ∀ u < vertexCount x, ∀ j, offset x u ≤ j → j < offset x (u + 1) →
    (u < leftCount x ↔ leftCount x ≤ target x j)

end Lax117284.BipartiteDecision
end
