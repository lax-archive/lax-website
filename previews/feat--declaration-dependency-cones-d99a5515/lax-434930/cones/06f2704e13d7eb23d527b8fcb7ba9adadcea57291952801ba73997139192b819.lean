-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax434930.SpaceMachines
section
namespace Lax434930.SpaceMachines.Configuration
end Lax434930.SpaceMachines.Configuration

namespace Lax434930.SpaceMachines.readInput
end Lax434930.SpaceMachines.readInput

namespace Lax434930.SpaceMachines.Machine.Run
end Lax434930.SpaceMachines.Machine.Run

namespace Lax434930.SpaceMachines.Move.apply
end Lax434930.SpaceMachines.Move.apply

set_option backward.isDefEq.respectTransparency false

namespace Lax434930.SpaceMachines

open PolynomialTime

/-- The input alphabet, with two distinct endmarkers. -/
inductive InputSymbol
  | leftEnd
  | bit (value : Bool)
  | rightEnd
  deriving DecidableEq, Fintype

/-- An elementary head movement, including staying in place. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq, Fintype

/-- One local transition: change state, write a work symbol, and move the heads. -/
structure Action (Γ Q : Type) where
  state : Q
  write : Γ
  inputMove : Move
  workMove : Move

/-- The complete finite description of a possibly nondeterministic machine. -/
structure Machine where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  blank : Γ
  start : Q
  transition : Q → InputSymbol → Γ → Finset (Action Γ Q)
  accept : Q → Bool

attribute [instance] Machine.alphabet Machine.control

end Lax434930.SpaceMachines
end

-- Lax434930.SpaceBounds
section
namespace Lax434930.SpaceBounds

open PolynomialTime SpaceMachines

/-- An integer logarithm that is positive even at input length zero. -/
def logSpace (n : ℕ) : ℕ := Nat.log 2 (n + 2)

end Lax434930.SpaceBounds
end
