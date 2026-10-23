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

/-- A language of finite binary strings. -/
abbrev Language := Set Word

end Lax434930.PolynomialTime
end

-- Lax115662.ProbabilisticMachines
section
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

/-- A uniform procedure with a worst-case polynomial bound on every branch. -/
structure Procedure (α : Type) where
  /-- The machine executing the procedure. -/
  machine : Machine
  /-- A polynomial bound on the number of steps on every computation branch. -/
  time : Polynomial ℕ
  /-- The answer associated with each terminal control state. -/
  output : machine.Q → α
  /-- Every coin sequence of the allowed length reaches a halting configuration. -/
  halts : ∀ (x : Word) (r : Fin (time.eval x.length) → Bool),
    TM0.step (machine.transition false) (machine.run x (List.ofFn r)) = none

/-- The finite sample space of coin sequences on a particular input. -/
abbrev Procedure.Coins {α : Type} (A : Procedure α) (x : Word) :=
  Fin (A.time.eval x.length) → Bool

/-- Read the output from the terminal control state. -/
def Procedure.eval {α : Type} (A : Procedure α) (x : Word) (r : A.Coins x) : α :=
  A.output (A.machine.run x (List.ofFn r)).q

/-- Exact probability under independent uniform bits. -/
noncomputable def Procedure.probability {α : Type} (A : Procedure α)
    (x : Word) (E : α → Prop) : ℚ :=
  ((Finset.univ.filter (fun r : A.Coins x => E (A.eval x r))).card : ℚ) /
    Fintype.card (A.Coins x)

/-- A Boolean answer correctly decides membership of the given input. -/
def Correct (L : Language) (x : Word) (b : Bool) : Prop :=
  (b = true ↔ x ∈ L)

end Lax115662.ProbabilisticMachines
end

-- Lax115662.RandomizedPolynomialTime
section
namespace Lax115662.RandomizedPolynomialTime

open Lax434930.PolynomialTime ProbabilisticMachines

def BPP : Set Language :=
  {L | ∃ A : Procedure Bool, ∀ x, (2 / 3 : ℚ) ≤ A.probability x (Correct L x)}

end Lax115662.RandomizedPolynomialTime
end

-- Lax115662.UnboundedError
section
namespace Lax115662.UnboundedError

open Lax434930.PolynomialTime ProbabilisticMachines

def PP : Set Language :=
  {L | ∃ A : Procedure Bool, ∀ x, (1 / 2 : ℚ) < A.probability x (Correct L x)}

end Lax115662.UnboundedError
end

-- Lax115662.BPPSubsetPP
section
namespace Lax115662.BPPSubsetPP

open RandomizedPolynomialTime UnboundedError

axiom BPP_subset_PP : BPP ⊆ PP

end Lax115662.BPPSubsetPP
end
