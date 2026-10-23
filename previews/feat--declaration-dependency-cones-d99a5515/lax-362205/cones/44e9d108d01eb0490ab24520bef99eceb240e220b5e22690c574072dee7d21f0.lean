-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Relation

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax434930.SpaceMachines
section
namespace Lax434930.SpaceMachines.Machine.Run
end Lax434930.SpaceMachines.Machine.Run

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

/-- Execute one action. The input head is clipped to the two endmarkers. -/
def Machine.execute (M : Machine) (w : Word) (c : M.Config)
    (a : Action M.Γ M.Q) : M.Config :=
  ⟨a.state, min (a.inputMove.apply c.inputHead) (w.length + 1),
    a.workMove.apply c.workHead, Function.update c.tape c.workHead a.write⟩

/-- One legal transition consults only the state and the two scanned symbols. -/
def Machine.Step (M : Machine) (w : Word) (c d : M.Config) : Prop :=
  ∃ a ∈ M.transition c.state (readInput w c.inputHead) (c.tape c.workHead),
    d = M.execute w c a

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

-- Lax362205.Reachability
section
namespace Lax362205.Reachability.Walk
end Lax362205.Reachability.Walk

namespace Lax362205.Reachability.search
end Lax362205.Reachability.search

set_option backward.isDefEq.respectTransparency false

namespace Lax362205.Reachability

abbrev Graph (N : ℕ) := Fin N → Fin N → Bool

end Lax362205.Reachability
end

-- Lax362205.ConfigurationGraph
section
set_option backward.isDefEq.respectTransparency false

namespace Lax362205.ConfigurationGraph

open scoped Classical

open Lax434930.PolynomialTime Lax434930.SpaceMachines BoundedConfigurations Reachability

/-- Label all bounded configurations consecutively from zero. -/
noncomputable def numbering (M : Machine) (n s : ℕ) :
    Config M n s ≃ Fin (Fintype.card (Config M n s)) := Fintype.equivFin _

/-- Connect two numbered configurations exactly when the machine can move from the first to the second. -/
noncomputable def graph (M : Machine) (w : Word) (s : ℕ) :
    Graph (Fintype.card (Config M w.length s)) :=
  fun a b => decide (M.Step w (expand ((numbering M w.length s).symm a))
    (expand ((numbering M w.length s).symm b)))

end Lax362205.ConfigurationGraph
end
