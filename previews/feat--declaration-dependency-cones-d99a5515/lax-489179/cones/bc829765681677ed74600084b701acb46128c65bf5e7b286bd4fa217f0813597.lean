-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

-- Lax489179.Satisfiability
section
namespace Lax489179.Satisfiability.Formula
end Lax489179.Satisfiability.Formula

namespace Lax489179.Satisfiability

abbrev Literal (n : ℕ) := Fin n × Bool

abbrev Clause (n : ℕ) := List (Literal n)

def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

def encodeLiteral {n : ℕ} (literal : Literal n) : List Bool :=
  encodeNat literal.1.val ++ [literal.2]

def encodeClause {n : ℕ} (clause : Clause n) : List Bool :=
  encodeNat clause.length ++ clause.flatMap encodeLiteral

end Lax489179.Satisfiability
end
