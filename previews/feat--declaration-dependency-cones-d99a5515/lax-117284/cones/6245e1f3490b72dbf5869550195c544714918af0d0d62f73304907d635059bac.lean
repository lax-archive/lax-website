-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Interval.Set.Basic

-- Lax117284.Scheduling
section
namespace Lax117284
end Lax117284

namespace Lax117284.Scheduling
end Lax117284.Scheduling

namespace Lax117284.Scheduling.Instance
end Lax117284.Scheduling.Instance
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
end Lax117284.ConflictGraph
end

-- Lax117284.InstanceEncoding
section
namespace Lax117284.InstanceEncoding.EncodesInstance
end Lax117284.InstanceEncoding.EncodesInstance

namespace Lax117284.InstanceEncoding

open Lax117284.Scheduling

/-- The number of clients declared by a word: its first entry. -/
def clientCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of days declared by a word: its second entry. -/
def dayCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The due date of client `j`'s job on day `i`: the due dates follow the processing
times. -/
def due (x : List ℕ) (i j : ℕ) : ℕ :=
  x.getD (2 + dayCount x * clientCount x + i * clientCount x + j) 0

end Lax117284.InstanceEncoding
end
