-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Tuple.Basic

-- Lax271696.Mso
section
namespace Lax271696.Mso.Sat
end Lax271696.Mso.Sat

namespace Lax271696.Mso

/-- Formulas of monadic second-order logic over the adjacency
signature, with `r` free vertex variables and `s` free set variables.
Vertex variables are `Fin r`, set variables are `Fin s`, and a
quantifier binds the *new last* index. -/
inductive MSO : ℕ → ℕ → Type
  /-- The vertices `i` and `j` are adjacent. -/
  | adj {r s : ℕ} (i j : Fin r) : MSO r s
  /-- The vertices `i` and `j` are equal. -/
  | eq {r s : ℕ} (i j : Fin r) : MSO r s
  /-- The vertex `i` belongs to the set `X`. -/
  | mem {r s : ℕ} (i : Fin r) (X : Fin s) : MSO r s
  /-- Negation. -/
  | not {r s : ℕ} (φ : MSO r s) : MSO r s
  /-- Conjunction. -/
  | and {r s : ℕ} (φ ψ : MSO r s) : MSO r s
  /-- There is a vertex satisfying `φ`, bound at the last index. -/
  | exV {r s : ℕ} (φ : MSO (r + 1) s) : MSO r s
  /-- There is a set of vertices satisfying `φ`, bound at the last
  index. -/
  | exS {r s : ℕ} (φ : MSO r (s + 1)) : MSO r s

/-- The quantifier rank: the nesting depth of quantifiers, counting
both kinds. -/
def rank : {r s : ℕ} → MSO r s → ℕ
  | _, _, .adj _ _ => 0
  | _, _, .eq _ _ => 0
  | _, _, .mem _ _ => 0
  | _, _, .not φ => rank φ
  | _, _, .and φ ψ => max (rank φ) (rank ψ)
  | _, _, .exV φ => rank φ + 1
  | _, _, .exS φ => rank φ + 1

variable {n : ℕ}

end Lax271696.Mso
end
