-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Log

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax689614.ArcKayles
section
namespace Lax689614.ArcKayles

variable {V : Type} [DecidableEq V]

/-- The position after playing an edge with endpoints `u` and `v`. -/
def remove (S : Finset V) (u v : V) : Finset V := (S.erase u).erase v

/-- Legal moves, represented by ordered pairs of endpoints. -/
noncomputable def moves (G : SimpleGraph V) (S : Finset V) : Finset (V × V) := by
  classical
  exact (S ×ˢ S).filter fun e => G.Adj e.1 e.2

/-- Winning for the next player, by backward induction on surviving vertices. -/
def Winning (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ e : {e // e ∈ moves G S}, ¬ Winning G (remove S e.val.1 e.val.2)
termination_by S.card
decreasing_by
  have h := e.property
  simp only [moves, Finset.mem_filter, Finset.mem_product] at h
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem h.1.1)

end Lax689614.ArcKayles
end

-- Lax689614.PositiveCNF
section
namespace Lax689614.PositiveCNF

structure Formula where
  nvars : ℕ
  clauses : List (Finset (Fin nvars))

def Satisfied (φ : Formula) (T : Finset (Fin φ.nvars)) : Prop :=
  ∀ C ∈ φ.clauses, ∃ x ∈ C, x ∈ T

/-- Whether True can force satisfaction from the specified position and turn. -/
def TrueWins (φ : Formula) (U T : Finset (Fin φ.nvars)) (trueTurn : Bool) : Prop :=
  if U = ∅ then Satisfied φ T
  else if trueTurn then
    ∃ x : U, TrueWins φ (U.erase x.val) (insert x.val T) false
  else
    ∀ x : U, TrueWins φ (U.erase x.val) T true
termination_by U.card
decreasing_by all_goals exact Finset.card_erase_lt_of_mem x.property

def FirstWins (φ : Formula) : Prop := TrueWins φ Finset.univ ∅ true

end Lax689614.PositiveCNF
end

-- Lax689614.Encoding
section
namespace Lax689614.Encoding
end Lax689614.Encoding

namespace Lax689614.Encoding.Graph
end Lax689614.Encoding.Graph
end

-- Lax689614.Construction
section
namespace Lax689614.Construction

open PositiveCNF

def K (φ : Formula) : ℕ := 4 * φ.nvars + 6

def R (φ : Formula) : ℕ := φ.clauses.length + 2 * φ.nvars + 2

def size (φ : Formula) : ℕ := 2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + 2 * K φ

def s : ℕ := 0

def t : ℕ := 1

def a (_φ : Formula) (j : ℕ) : ℕ := 2 + j

def b (φ : Formula) (j : ℕ) : ℕ := 2 + φ.clauses.length + j

def v (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + i

def vt (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + R φ + i

def f (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + 2 * R φ + i

def y (φ : Formula) (i : ℕ) : ℕ :=
  2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + i

def z (φ : Formula) (i : ℕ) : ℕ :=
  2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + K φ + i

def Edge (φ : Formula) (u w : ℕ) : Prop :=
  (u = s ∧ w = t) ∨
  (∃ j < φ.clauses.length, u = s ∧ w = a φ j) ∨
  (∃ j < φ.clauses.length, u = a φ j ∧ w = b φ j) ∨
  (∃ j < φ.clauses.length, ∃ i < R φ, u = b φ j ∧ w = v φ i) ∨
  (∃ i < R φ, u = v φ i ∧ w = vt φ i) ∨
  (∃ i < φ.nvars, u = v φ i ∧ w = f φ i) ∨
  (∃ j : Fin φ.clauses.length, ∃ i ∈ φ.clauses[j],
    u = b φ j ∧ w = f φ i) ∨
  (∃ i < K φ, u = s ∧ w = y φ i) ∨
  (∃ i < K φ, u = y φ i ∧ w = z φ i)

def graph (φ : Formula) : SimpleGraph ℕ := SimpleGraph.fromRel (Edge φ)

def board (φ : Formula) : Finset ℕ := Finset.range (size φ)

end Lax689614.Construction
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
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
end Lax434930.SpaceBounds
end

-- Lax434930.PolynomialSpace
section
namespace Lax434930.PolynomialSpace
end Lax434930.PolynomialSpace
end

-- Lax689614.PSPACE
section
namespace Lax689614
end Lax689614

namespace Lax689614.PSPACE
end Lax689614.PSPACE
end

-- Lax689614.Reduction
section
namespace Lax689614.Reduction

open PositiveCNF Construction ArcKayles

axiom true_strategy (φ : Formula) (hm : φ.clauses.length % 2 = 1)
    (h : FirstWins φ) : Winning (graph φ) (board φ)

end Lax689614.Reduction
end
