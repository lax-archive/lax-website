-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic

-- Lax342547.FingerprintCounts
section
namespace Lax342547.FingerprintCounts

noncomputable def pad {U : Type} (L : ℕ) (l : List U) : List (Option U) :=
  l.map some ++ List.replicate (L-l.length) none

end Lax342547.FingerprintCounts
end
