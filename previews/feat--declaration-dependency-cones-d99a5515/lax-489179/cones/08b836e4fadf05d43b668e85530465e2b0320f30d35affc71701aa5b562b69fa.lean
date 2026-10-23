-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

-- Lax489179.Satisfiability
section
namespace Lax489179.Satisfiability

abbrev Literal (n : ℕ) := Fin n × Bool

abbrev Clause (n : ℕ) := List (Literal n)

structure Formula where
  numVars : ℕ
  clauses : List (Clause numVars)

def WidthAtMost (k : ℕ) (F : Formula) : Prop :=
  ∀ clause ∈ F.clauses, clause.length ≤ k

end Lax489179.Satisfiability
end
