-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Tuple.Basic

-- Lax3.FirstOrder
section
namespace Lax3.FirstOrder.Sat
end Lax3.FirstOrder.Sat

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

/-- The quantifier rank: the nesting depth of quantifiers. -/
def rank : {k : ℕ} → FO k → ℕ
  | _, .adj _ _ => 0
  | _, .eq _ _ => 0
  | _, .not φ => rank φ
  | _, .and φ ψ => max (rank φ) (rank ψ)
  | _, .ex φ => rank φ + 1

variable {n : ℕ}

end Lax3.FirstOrder
end
