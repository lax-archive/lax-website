-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax251941.PostCorrespondence
section
namespace Lax251941.PostCorrespondence

/-- The concatenation of the strings of `ws` selected by a list of indices. -/
def conc (ws : List (List ℕ)) (idx : List ℕ) : List ℕ :=
  (idx.map (fun i => ws.getD i [])).flatten

end Lax251941.PostCorrespondence
end
