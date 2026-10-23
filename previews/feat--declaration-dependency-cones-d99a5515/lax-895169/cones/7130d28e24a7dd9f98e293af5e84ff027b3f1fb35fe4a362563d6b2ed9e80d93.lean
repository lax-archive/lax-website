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

/-- A quantifier prefix, peeled from the innermost variable outwards: the
variable of index `0` is quantified outermost, existentially when its polarity
is `true`. -/
def prefixHolds {A : Type} : (m : ℕ) → (Fin m → Bool) → ((Fin m → A) → Prop) → Prop
  | 0, _, P => P Fin.elim0
  | m + 1, pol, P =>
      prefixHolds m (fun j => pol j.castSucc)
        (fun v => if pol (Fin.last m) = true then ∃ a, P (Fin.snoc v a)
          else ∀ a, P (Fin.snoc v a))

end Lax895169.BitPredicate
end

-- Lax904597.Problems
section
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

instance instCoeFun : CoeFun (DecisionProblem L) fun _ => ∀ (A : Type) [L.Structure A], Prop :=
  ⟨Holds⟩

end DecisionProblem

end Lax904597.Problems
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

/-- **A sentence of the bit-level logic, in prenex form**: a polarity per
variable and a quantifier-free kernel. -/
structure BitSentence (L : Language.{0, 0}) where
  /-- The number of quantified variables. -/
  vars : ℕ
  /-- The quantifier at each variable: `true` existential, `false` universal. -/
  pol : Fin vars → Bool
  /-- The quantifier-free kernel. -/
  kernel : BitKernel L (Fin vars)

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

/-- What a sentence says of an instance: the prefix, played over the kernel. -/
def Holds {L : Language.{0, 0}} (φ : BitSentence L) (A : Type) [L.Structure A] [LinearOrder A]
    [Finite A] : Prop :=
  prefixHolds (A := A) φ.vars φ.pol fun v => φ.kernel.Holds v

end BitSentence

/-- A decision problem is **bit-definable** when a prenex sentence over the
order, the addition and the bit at an index – `FO(≤, +, BIT)` – decides it on
every nonempty finite ordered structure. -/
def BitDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ φ : BitSentence L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ φ.Holds A

end Lax895169.BitLogic
end
