-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Computability.NFA

-- Lax52.NFARecognizable
section
namespace Lax52.NFARecognizable

universe u

/-- Recognition by an NFA with a finite state type. -/
def NFARecognizable {Sigma : Type u} (L : _root_.Language Sigma) : Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, ∃ M : NFA Sigma Q, M.accepts = L

end Lax52.NFARecognizable
end
