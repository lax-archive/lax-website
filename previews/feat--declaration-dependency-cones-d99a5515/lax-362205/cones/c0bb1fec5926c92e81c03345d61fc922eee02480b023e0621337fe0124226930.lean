-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax434930.SpaceMachines
section
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

/-- The two head positions, control state, and work-tape contents. -/
structure Configuration (Γ Q : Type) where
  state : Q
  inputHead : ℕ
  workHead : ℕ
  tape : ℕ → Γ

/-- Configurations for a fixed machine. Only reachable configurations are used. -/
abbrev Machine.Config (M : Machine) := Configuration M.Γ M.Q

end Lax434930.SpaceMachines
end

-- Lax362205.BoundedConfigurations
section
set_option backward.isDefEq.respectTransparency false

namespace Lax362205.BoundedConfigurations

open Lax434930.SpaceMachines

structure Config (M : Machine) (n s : ℕ) where
  state : M.Q
  inputHead : Fin (n + 2)
  workHead : Fin s
  tape : Fin s → M.Γ
  deriving Fintype

def expand {M : Machine} {n s : ℕ} (c : Config M n s) : M.Config :=
  ⟨c.state, c.inputHead.val, c.workHead.val,
    fun i => if h : i < s then c.tape ⟨i, h⟩ else M.blank⟩

end Lax362205.BoundedConfigurations
end
