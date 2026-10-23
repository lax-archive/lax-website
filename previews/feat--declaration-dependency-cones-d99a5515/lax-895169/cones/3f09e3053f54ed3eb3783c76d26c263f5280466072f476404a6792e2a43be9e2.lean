-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Order.Basic

-- Lax895169.BitPredicate
section
namespace Lax895169.BitPredicate.prefixHolds
end Lax895169.BitPredicate.prefixHolds

namespace Lax895169.BitPredicate

/-- The rank of an element of a finite linear order: the number of its strict
predecessors. -/
noncomputable def orank {A : Type} [LinearOrder A] (z : A) : ℕ :=
  {y : A | y < z}.ncard

/-- **The number of bit positions** of the ranks of `A`: the ranks are the
numbers below `Nat.card A`, so they are exactly the numbers whose bits live
below `Nat.clog 2 (Nat.card A)`. -/
noncomputable def posCount (A : Type) [LinearOrder A] [Finite A] : ℕ :=
  Nat.clog 2 (Nat.card A)

end Lax895169.BitPredicate
end

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax895169.LogTimeMachines
section
namespace Lax895169.LogTimeMachines.LTMachine
end Lax895169.LogTimeMachines.LTMachine

namespace Lax895169.LogTimeMachines.BaseTest.Holds
end Lax895169.LogTimeMachines.BaseTest.Holds

namespace Lax895169.LogTimeMachines.BaseTest.and
end Lax895169.LogTimeMachines.BaseTest.and

namespace Lax895169.LogTimeMachines.BaseTest.bit
end Lax895169.LogTimeMachines.BaseTest.bit

namespace Lax895169.LogTimeMachines.BaseTest.not
end Lax895169.LogTimeMachines.BaseTest.not

namespace Lax895169.LogTimeMachines.BaseTest.or
end Lax895169.LogTimeMachines.BaseTest.or

namespace Lax895169.LogTimeMachines.BaseTest.query
end Lax895169.LogTimeMachines.BaseTest.query

namespace Lax895169.LogTimeMachines.BaseTest.sweep
end Lax895169.LogTimeMachines.BaseTest.sweep

namespace Lax895169.LogTimeMachines

open Lax895169.BitPredicate Lax904597.Problems

open FirstOrder

open Language Structure

/-- A Boolean expression over bit variables: what a sweep computes in one step,
and what its acceptance condition is. Expressions rather than functions, so that
the translation into a formula is a recursion rather than an enumeration of a
truth table. -/
inductive BitExpr (V : Type) where
  /-- A bit variable. -/
  | var (v : V) : BitExpr V
  /-- The constant `true`. -/
  | tt : BitExpr V
  /-- The constant `false`. -/
  | ff : BitExpr V
  /-- Negation. -/
  | not (e : BitExpr V) : BitExpr V
  /-- Conjunction. -/
  | and (e f : BitExpr V) : BitExpr V
  /-- Disjunction. -/
  | or (e f : BitExpr V) : BitExpr V

namespace BitExpr

variable {V : Type}

/-- The value of an expression under a `Bool`-valued assignment. -/
def eval (val : V → Bool) : BitExpr V → Bool
  | .var v => val v
  | .tt => true
  | .ff => false
  | .not e => !(e.eval val)
  | .and e f => e.eval val && f.eval val
  | .or e f => e.eval val || f.eval val

end BitExpr

/-- A **sweep**: one pass over the bit positions of the universe, from the
lowest to the highest, by a finite automaton with `σ` state bits reading, at
each position, one bit of each of the `ρ` registers. -/
structure Sweep (ρ : ℕ) where
  /-- The number of state bits. -/
  σ : ℕ
  /-- The state before the lowest position. -/
  init : Fin σ → Bool
  /-- The next state: one Boolean expression per state bit, over the old state
  and the register bits at the current position. -/
  step : Fin σ → BitExpr (Fin σ ⊕ Fin ρ)
  /-- The acceptance condition, read from the state after the last position. -/
  acc : BitExpr (Fin σ)

namespace Sweep

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

/-- **The state of a sweep before position `i`**: the automaton starts in its
initial state and takes one step per position, reading the bits of the
registers there. -/
noncomputable def state (S : Sweep ρ) (x : Fin ρ → A) : ℕ → (Fin S.σ → Bool)
  | 0 => S.init
  | i + 1 => fun j => (S.step j).eval
      (Sum.elim (state S x i) fun k => (orank (x k)).testBit i)

/-- **A sweep accepts** when its acceptance condition holds of the state left
after the last bit position. -/
def Accepts (S : Sweep ρ) (x : Fin ρ → A) : Prop :=
  S.acc.eval (S.state x (posCount A)) = true

end Sweep

namespace BaseTest

variable {L : Language.{0, 0}} {ρ : ℕ}

end BaseTest

end Lax895169.LogTimeMachines
end
