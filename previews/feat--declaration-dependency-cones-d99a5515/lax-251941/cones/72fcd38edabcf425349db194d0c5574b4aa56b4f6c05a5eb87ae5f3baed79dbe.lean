-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax251941.PostCorrespondence
section
namespace Lax251941.PostCorrespondence

/-- A domino: a top string and a bottom string. -/
abbrev Domino (α : Type*) := List α × List α

/-- An instance of the Post correspondence problem: a finite list of dominos. -/
abbrev Inst (α : Type*) := List (Domino α)

/-- The string read off the top halves of a sequence of dominos. -/
def topStr {α : Type*} (s : List (Domino α)) : List α := (s.map Prod.fst).flatten

/-- The string read off the bottom halves of a sequence of dominos. -/
def botStr {α : Type*} (s : List (Domino α)) : List α := (s.map Prod.snd).flatten

/-- `s` is a match of the instance `P`: a nonempty sequence of dominos of `P`
whose top string equals its bottom string. -/
def IsMatch {α : Type*} (P : Inst α) (s : List (Domino α)) : Prop :=
  s ≠ [] ∧ (∀ d ∈ s, d ∈ P) ∧ topStr s = botStr s

/-- The instance `P` has a match. -/
def HasMatch {α : Type*} (P : Inst α) : Prop := ∃ s, IsMatch P s

end Lax251941.PostCorrespondence
end
