-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax251941.PostCorrespondence
section
namespace Lax251941.PostCorrespondence

/-- An instance in index form: a finite list of pairs of strings over `ℕ`. -/
abbrev Instance := List (List ℕ × List ℕ)

/-- The concatenation of the strings of `ws` selected by a list of indices. -/
def conc (ws : List (List ℕ)) (idx : List ℕ) : List ℕ :=
  (idx.map (fun i => ws.getD i [])).flatten

/-- An instance is solvable if some nonempty sequence of indices makes the two
concatenations equal. -/
def Solvable (P : Instance) : Prop :=
  ∃ idx : List ℕ, idx ≠ [] ∧ (∀ i ∈ idx, i < P.length) ∧
    conc (P.map Prod.fst) idx = conc (P.map Prod.snd) idx

end Lax251941.PostCorrespondence
end
