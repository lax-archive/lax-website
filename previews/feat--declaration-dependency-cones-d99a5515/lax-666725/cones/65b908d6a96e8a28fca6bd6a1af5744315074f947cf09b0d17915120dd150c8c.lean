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

-- Lax666725.ProbabilisticMachines
section
namespace Lax666725.ProbabilisticMachines

open Lax434930.PolynomialTime Turing

/-- Two finite local transition tables, with common halting configurations. -/
structure Machine where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  [blank : Inhabited Γ]
  [initial : Inhabited Q]
  input : Bool ↪ Γ
  input_ne_blank : ∀ b, input b ≠ default
  transition : Bool → TM0.Machine Γ Q
  same_halts : ∀ q a, transition false q a = none ↔ transition true q a = none

attribute [instance] Machine.alphabet Machine.control Machine.blank Machine.initial

/-- Perform one coin-selected transition, keeping terminal configurations fixed. -/
def Machine.advance (M : Machine) (c : TM0.Cfg M.Γ M.Q) (b : Bool) :
    TM0.Cfg M.Γ M.Q :=
  (TM0.step (M.transition b) c).getD c

/-- Execute a finite sequence of fair coin choices. -/
def Machine.run (M : Machine) (x coins : Word) : TM0.Cfg M.Γ M.Q :=
  coins.foldl M.advance (TM0.init (x.map M.input))

/-- A uniform procedure with a worst-case polynomial bound on every branch. -/
structure Procedure (α : Type) where
  machine : Machine
  time : Polynomial ℕ
  output : machine.Q → α
  halts : ∀ (x : Word) (r : Fin (time.eval x.length) → Bool),
    TM0.step (machine.transition false) (machine.run x (List.ofFn r)) = none

/-- The finite sample space of coin sequences on a particular input. -/
abbrev Procedure.Coins {α : Type} (A : Procedure α) (x : Word) :=
  Fin (A.time.eval x.length) → Bool

/-- Read the output from the terminal control state. -/
def Procedure.eval {α : Type} (A : Procedure α) (x : Word) (r : A.Coins x) : α :=
  A.output (A.machine.run x (List.ofFn r)).q

end Lax666725.ProbabilisticMachines
end
