-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.NFA

-- Lax146103.NFARecognizable
section
namespace Lax146103.NFARecognizable

universe u

/-- Recognition by an NFA with a finite state type. -/
def NFARecognizable {Sigma : Type u} (L : _root_.Language Sigma) : Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, ∃ M : NFA Sigma Q, M.accepts = L

end Lax146103.NFARecognizable
end
