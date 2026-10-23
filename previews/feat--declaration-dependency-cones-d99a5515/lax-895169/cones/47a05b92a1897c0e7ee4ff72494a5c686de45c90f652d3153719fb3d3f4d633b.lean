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

/-- **The bit of `x` at the index `i`**: the `BIT` of the classical vocabulary
`FO(≤, BIT)`, the position being named by the element whose *rank* is the
exponent. Total, and with no guard – above the bit positions of the universe
every bit is simply clear. -/
def BitIx {A : Type} [LinearOrder A] (i x : A) : Prop :=
  (orank x).testBit (orank i) = true

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

-- Lax895169.BitLogic
section
namespace Lax895169.BitLogic

open Lax895169.BitPredicate Lax904597.Problems

open FirstOrder

open Language Structure

/-- The atoms of the bit-level logic: the order, the addition of ranks, the bit
of an element at an index, and an input relation at a tuple of variables. -/
inductive BitAtom (L : Language.{0, 0}) (γ : Type) where
  /-- `x ≤ y`. -/
  | le (x y : γ) : BitAtom L γ
  /-- `orank x + orank y = orank z`. -/
  | plus (x y z : γ) : BitAtom L γ
  /-- The bit of `x` at the index `i` is set. -/
  | bit (i x : γ) : BitAtom L γ
  /-- An input relation at a tuple of variables. -/
  | rel {a : ℕ} (R : L.Relations a) (arg : Fin a → γ) : BitAtom L γ

/-- A quantifier-free kernel over the bit-level atoms. -/
inductive BitKernel (L : Language.{0, 0}) (γ : Type) where
  /-- An atom. -/
  | atom (a : BitAtom L γ) : BitKernel L γ
  /-- The constant `true`, so that a trivial relation needs no dummy variable. -/
  | tt : BitKernel L γ
  /-- Negation. -/
  | not (k : BitKernel L γ) : BitKernel L γ
  /-- Conjunction. -/
  | and (k k' : BitKernel L γ) : BitKernel L γ
  /-- Disjunction. -/
  | or (k k' : BitKernel L γ) : BitKernel L γ

namespace BitAtom

variable {L : Language.{0, 0}} {γ : Type}

/-- What an atom says of a valuation. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BitAtom L γ → (γ → A) → Prop
  | .le x y, v => v x ≤ v y
  | .plus x y z, v => orank (v x) + orank (v y) = orank (v z)
  | .bit i x, v => BitIx (v i) (v x)
  | .rel R arg, v => RelMap R fun t => v (arg t)

end BitAtom

namespace BitKernel

variable {L : Language.{0, 0}} {γ : Type}

/-- What a kernel says of a valuation. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BitKernel L γ → (γ → A) → Prop
  | .atom a, v => a.Holds v
  | .tt, _ => True
  | .not k, v => ¬ k.Holds v
  | .and k k', v => k.Holds v ∧ k'.Holds v
  | .or k k', v => k.Holds v ∨ k'.Holds v

end BitKernel

namespace BitSentence

end BitSentence

end Lax895169.BitLogic
end
