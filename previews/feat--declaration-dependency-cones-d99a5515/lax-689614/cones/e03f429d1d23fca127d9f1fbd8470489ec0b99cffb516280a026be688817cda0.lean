-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

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
namespace Lax689614.PositiveCNF.TrueWins
end Lax689614.PositiveCNF.TrueWins

namespace Lax689614.PositiveCNF

structure Formula where
  nvars : ℕ
  clauses : List (Finset (Fin nvars))

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

-- Lax689614.Grundy
section
namespace Lax689614.Grundy
end Lax689614.Grundy

namespace Lax689614.Grundy.value
end Lax689614.Grundy.value
end

-- Lax689614.RegularPlay
section
namespace Lax689614.RegularPlay

open PositiveCNF Construction ArcKayles

def SameEdge (u w x z : ℕ) : Prop := (u = x ∧ w = z) ∨ (u = z ∧ w = x)

def RegularMove (φ : Formula) (u w : ℕ) : Prop :=
  (∃ i < R φ, SameEdge u w (v φ i) (vt φ i)) ∨
  (∃ i < φ.nvars, SameEdge u w (v φ i) (f φ i)) ∨
  (∃ i < K φ, SameEdge u w (y φ i) (z φ i))

inductive Reachable (φ : Formula) : Finset ℕ → Prop
  | initial : Reachable φ (board φ)
  | step {S : Finset ℕ} {u w : ℕ} : Reachable φ S →
      u ∈ S → w ∈ S → (graph φ).Adj u w → RegularMove φ u w →
      Reachable φ (remove S u w)

def remainingV (φ : Formula) (S : Finset ℕ) : ℕ :=
  ((Finset.range (R φ)).filter fun i => v φ i ∈ S).card

def remainingY (φ : Formula) (S : Finset ℕ) : ℕ :=
  ((Finset.range (K φ)).filter fun i => y φ i ∈ S).card

def Exhausted (φ : Formula) (S : Finset ℕ) (j : Fin φ.clauses.length) : Prop :=
  ∀ i ∈ φ.clauses[j], f φ i ∉ S

def Exceptional (φ : Formula) (S : Finset ℕ) (u w : ℕ) : Prop :=
  ∃ j : Fin φ.clauses.length, SameEdge u w s (a φ j) ∧ Exhausted φ S j

axiom deviation_loses (φ : Formula) (hm : φ.clauses.length % 2 = 1)
    (S : Finset ℕ) (hS : Reachable φ S)
    (hr : φ.clauses.length ≤ remainingV φ S) (hk : 1 ≤ remainingY φ S)
    (u w : ℕ) (hu : u ∈ S) (hw : w ∈ S) (he : (graph φ).Adj u w)
    (hn : ¬ RegularMove φ u w) (hx : ¬ Exceptional φ S u w) :
    Winning (graph φ) (remove S u w)

end Lax689614.RegularPlay
end
