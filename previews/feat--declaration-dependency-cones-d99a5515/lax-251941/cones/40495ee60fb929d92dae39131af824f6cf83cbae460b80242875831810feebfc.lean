-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.PartrecCode

-- Lax251941.Acceptance
section
namespace Lax251941.Acceptance

/-- A machine: a partial recursive program. -/
abbrev Machine := Nat.Partrec.Code

/-- `M` accepts `w` if it halts on `w` with output `1`. -/
def Accepts (M : Machine) (w : ℕ) : Prop := M.eval w = Part.some 1

/-- `M` rejects `w` if it halts on `w` with output `0`. -/
def Rejects (M : Machine) (w : ℕ) : Prop := M.eval w = Part.some 0

/-- A machine is a decider if it accepts or rejects every input, i.e. never loops.
-/
def IsDecider (M : Machine) : Prop := ∀ w, Accepts M w ∨ Rejects M w

/-- `M` recognises the language `A` if it accepts exactly the words of `A`. -/
def Recognizes (M : Machine) (A : Set ℕ) : Prop := ∀ w, w ∈ A ↔ Accepts M w

/-- `M` decides `A` if it is a decider that recognises `A`. -/
def Decides (M : Machine) (A : Set ℕ) : Prop := IsDecider M ∧ Recognizes M A

end Lax251941.Acceptance
end
