-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Tuple.Basic

-- Lax3.FirstOrder
section
namespace Lax3.FirstOrder.Sat
end Lax3.FirstOrder.Sat

namespace Lax3.FirstOrder.rank
end Lax3.FirstOrder.rank

namespace Lax3.FirstOrder

/-- Formulas of first-order logic over the adjacency signature, with
`k` free variables. Variables are `Fin k`, and the quantifier binds the
*new last* index. -/
inductive FO : ℕ → Type
  /-- The vertices `i` and `j` are adjacent. -/
  | adj {k : ℕ} (i j : Fin k) : FO k
  /-- The vertices `i` and `j` are equal. -/
  | eq {k : ℕ} (i j : Fin k) : FO k
  /-- Negation. -/
  | not {k : ℕ} (φ : FO k) : FO k
  /-- Conjunction. -/
  | and {k : ℕ} (φ ψ : FO k) : FO k
  /-- There is a vertex satisfying `φ`, bound at the last index. -/
  | ex {k : ℕ} (φ : FO (k + 1)) : FO k

variable {n : ℕ}

end Lax3.FirstOrder
end
