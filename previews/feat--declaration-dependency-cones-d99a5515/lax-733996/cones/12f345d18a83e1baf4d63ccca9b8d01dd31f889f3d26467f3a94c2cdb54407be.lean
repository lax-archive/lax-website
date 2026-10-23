-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
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

/-- No choice of action is available at a terminal configuration. -/
def Machine.Terminal (M : Machine) (w : Word) (c : M.Config) : Prop :=
  ∀ d : M.Config, ¬ M.Step w c d

end Lax434930.SpaceMachines
end

-- Lax733996.BoundedConfigurations
section
set_option backward.isDefEq.respectTransparency false

namespace Lax733996.BoundedConfigurations

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

end Lax733996.BoundedConfigurations
end

-- Lax733996.Reachability
section
namespace Lax733996.Reachability.search
end Lax733996.Reachability.search

set_option backward.isDefEq.respectTransparency false

namespace Lax733996.Reachability

abbrev Graph (N : ℕ) := Fin N → Fin N → Bool

inductive Walk {α : Type} (R : α → α → Prop) : ℕ → α → α → Prop
  | nil (a : α) : Walk R 0 a a
  | tail {n : ℕ} {a b c : α} : Walk R n a b → R b c → Walk R (n + 1) a c

def Within {α : Type} (R : α → α → Prop) (n : ℕ) (a b : α) : Prop :=
  ∃ k ≤ n, Walk R k a b

end Lax733996.Reachability
end

-- Lax733996.ConfigurationGraph
section
set_option backward.isDefEq.respectTransparency false

namespace Lax733996.ConfigurationGraph

open Lax434930.PolynomialTime Lax434930.SpaceMachines BoundedConfigurations Reachability

noncomputable def numbering (M : Machine) (n s : ℕ) :
    Config M n s ≃ Fin (Fintype.card (Config M n s)) := Fintype.equivFin _

noncomputable def graph (M : Machine) (w : Word) (s : ℕ) :
    Graph (Fintype.card (Config M w.length s)) := by
  classical
  exact fun a b => decide (M.Step w (expand ((numbering M w.length s).symm a))
    (expand ((numbering M w.length s).symm b)))

end Lax733996.ConfigurationGraph
end

-- Lax733996.Counting
section
namespace Lax733996.Counting

open Lax733996.Reachability

def Census {N : ℕ} (G : Graph N) (a : Fin N) (k c : ℕ) (S : Finset (Fin N)) : Prop :=
  S.card = c ∧ ∀ v ∈ S, Within (fun u v => G u v = true) k a v

def Classify {N : ℕ} (G : Graph N) (a : Fin N) (k c : ℕ) (v : Fin N) : Bool → Prop
  | true => Within (fun u v => G u v = true) (k + 1) a v
  | false => ∃ S, Census G a k c S ∧ v ≠ a ∧ ∀ u ∈ S, G u v = false

def CountStep {N : ℕ} (G : Graph N) (a : Fin N) (k c d : ℕ) : Prop :=
  ∃ answers : Fin N → Bool, (∀ v, Classify G a k c v (answers v)) ∧
    (Finset.univ.filter (fun v => answers v = true)).card = d

def CountTrace {N : ℕ} (G : Graph N) (a : Fin N) (counts : ℕ → ℕ) : Prop :=
  counts 0 = 1 ∧ ∀ k < N, CountStep G a k (counts k) (counts (k + 1))

def NonreachCertificate {N : ℕ} (G : Graph N) (a b : Fin N) : Prop :=
  ∃ counts, CountTrace G a counts ∧
    ∃ S, Census G a N (counts N) S ∧ b ∉ S

end Lax733996.Counting
end

-- Lax733996.ConfigurationCounting
section
namespace Lax733996.ConfigurationCounting

open Lax434930.PolynomialTime Lax434930.SpaceMachines

open Lax733996.BoundedConfigurations Lax733996.ConfigurationGraph Counting

def RejectsByCounting (M : Machine) (w : Word) (s : ℕ) : Prop :=
  ∀ a b : Config M w.length s, expand a = M.initial →
    M.Terminal w (expand b) → M.accept b.state = true →
    NonreachCertificate (graph M w s) (numbering M w.length s a) (numbering M w.length s b)

end Lax733996.ConfigurationCounting
end
