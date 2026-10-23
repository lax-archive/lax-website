-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax251941.PostCorrespondence
section
namespace Lax251941.PostCorrespondence

/-- A domino: a top string and a bottom string. -/
abbrev Domino (α : Type*) := List α × List α

/-- The string read off the bottom halves of a sequence of dominos. -/
def botStr {α : Type*} (s : List (Domino α)) : List α := (s.map Prod.snd).flatten

end Lax251941.PostCorrespondence
end
