-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax251941.PostCorrespondence
section
namespace Lax251941.PostCorrespondence

/-- An instance in index form: a finite list of pairs of strings over `ℕ`. -/
abbrev Instance := List (List ℕ × List ℕ)

end Lax251941.PostCorrespondence
end
