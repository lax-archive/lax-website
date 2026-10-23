-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Basic

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

end Lax434930.PolynomialTime
end

-- Lax434930.SpaceMachines
section
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

/-- Move a head on a semi-infinite tape, keeping it at zero on a leftward exit. -/
def Move.apply : Move → ℕ → ℕ
  | .left, i => i - 1
  | .stay, i => i
  | .right, i => i + 1

/-- Read the immutable input at a head position, including its endmarkers. -/
def readInput (w : Word) : ℕ → InputSymbol
  | 0 => .leftEnd
  | i + 1 => match w[i]? with
    | some b => .bit b
    | none => .rightEnd

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

/-- The work tape is blank; the input is supplied separately to the step relation. -/
def Machine.initial (M : Machine) : M.Config :=
  ⟨M.start, 0, 0, fun _ => M.blank⟩

/-- Execute one action. The input head is clipped to the two endmarkers. -/
def Machine.execute (M : Machine) (w : Word) (c : M.Config)
    (a : Action M.Γ M.Q) : M.Config :=
  ⟨a.state, min (a.inputMove.apply c.inputHead) (w.length + 1),
    a.workMove.apply c.workHead, Function.update c.tape c.workHead a.write⟩

/-- One legal transition consults only the state and the two scanned symbols. -/
def Machine.Step (M : Machine) (w : Word) (c d : M.Config) : Prop :=
  ∃ a ∈ M.transition c.state (readInput w c.inputHead) (c.tape c.workHead),
    d = M.execute w c a

/-- A computation prefix consisting of exactly the indicated number of transitions. -/
inductive Machine.Run (M : Machine) (w : Word) : ℕ → M.Config → Prop
  | zero : M.Run w 0 M.initial
  | succ {n : ℕ} {c d : M.Config} :
      M.Run w n c → M.Step w c d → M.Run w (n + 1) d

/-- No choice of action is available at a terminal configuration. -/
def Machine.Terminal (M : Machine) (w : Word) (c : M.Config) : Prop :=
  ∀ d : M.Config, ¬ M.Step w c d

/-- All computation branches on this input have bounded finite length. -/
def Machine.HaltsOn (M : Machine) (w : Word) : Prop :=
  ∃ t : ℕ, ∀ (n : ℕ) (c : M.Config), M.Run w n c → n ≤ t

/-- Existential acceptance at a terminal configuration. -/
def Machine.Accepts (M : Machine) (w : Word) : Prop :=
  ∃ (n : ℕ) (c : M.Config), M.Run w n c ∧ M.Terminal w c ∧ M.accept c.state = true

/-- A decider halts on every branch and accepts exactly its language. -/
def Machine.Decides (M : Machine) (A : Language) : Prop :=
  ∀ w : Word, M.HaltsOn w ∧ (M.Accepts w ↔ w ∈ A)

end Lax434930.SpaceMachines
end
