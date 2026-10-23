-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax115662.ProbabilisticMachines
section
namespace Lax115662.ProbabilisticMachines.Procedure
end Lax115662.ProbabilisticMachines.Procedure

namespace Lax115662.ProbabilisticMachines

open scoped Classical

open Lax434930.PolynomialTime Turing

/-- Two finite local transition tables, with common halting configurations. -/
structure Machine where
  /-- The finite tape alphabet. -/
  Γ : Type
  /-- The finite set of control states. -/
  Q : Type
  /-- There are finitely many tape symbols. -/
  [alphabet : Fintype Γ]
  /-- There are finitely many control states. -/
  [control : Fintype Q]
  /-- The distinguished blank tape symbol. -/
  [blank : Inhabited Γ]
  /-- The initial control state. -/
  [initial : Inhabited Q]
  /-- Represent each binary input symbol as a tape symbol. -/
  input : Bool ↪ Γ
  /-- Input symbols are distinct from the blank symbol. -/
  input_ne_blank : ∀ b, input b ≠ default
  /-- One transition table for each possible coin outcome. -/
  transition : Bool → TM0.Machine Γ Q
  /-- Whether a configuration halts is independent of the next coin. -/
  same_halts : ∀ q a, transition false q a = none ↔ transition true q a = none

attribute [instance] Machine.alphabet Machine.control Machine.blank Machine.initial

/-- Perform one coin-selected transition, keeping terminal configurations fixed. -/
def Machine.advance (M : Machine) (c : TM0.Cfg M.Γ M.Q) (b : Bool) :
    TM0.Cfg M.Γ M.Q :=
  (TM0.step (M.transition b) c).getD c

/-- Execute a finite sequence of fair coin choices. -/
def Machine.run (M : Machine) (x coins : Word) : TM0.Cfg M.Γ M.Q :=
  coins.foldl M.advance (TM0.init (x.map M.input))

end Lax115662.ProbabilisticMachines
end
