-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Tuple.Basic

-- Lax11.Mso
section
namespace Lax11.Mso.rank
end Lax11.Mso.rank

namespace Lax11.Mso

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

variable {n : ℕ}

/-- Satisfaction of a formula in the graph `G`, under a vertex
environment `m` and a set environment `A`. -/
def Sat (G : SimpleGraph (Fin n)) :
    {r s : ℕ} → (Fin r → Fin n) → (Fin s → Set (Fin n)) → MSO r s → Prop
  | _, _, m, _, .adj i j => G.Adj (m i) (m j)
  | _, _, m, _, .eq i j => m i = m j
  | _, _, m, A, .mem i X => m i ∈ A X
  | _, _, m, A, .not φ => ¬ Sat G m A φ
  | _, _, m, A, .and φ ψ => Sat G m A φ ∧ Sat G m A ψ
  | _, _, m, A, .exV φ => ∃ v : Fin n, Sat G (Fin.snoc m v) A φ
  | _, _, m, A, .exS φ => ∃ S : Set (Fin n), Sat G m (Fin.snoc A S) φ

end Lax11.Mso
end
