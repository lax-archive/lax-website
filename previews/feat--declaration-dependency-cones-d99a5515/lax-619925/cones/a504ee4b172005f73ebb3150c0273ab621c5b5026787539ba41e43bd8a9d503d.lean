-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic

-- Lax619925.Series
section
namespace Lax619925.Series

set_option linter.dupNamespace false in
/-- A formal power series over the alphabet `α`: a function from words to `ℚ`. -/
abbrev Series (α : Type*) := List α → ℚ

/-- Two words are *commutatively equivalent* if they have the same multiset of letters,
    i.e. one is obtained from the other by permuting the positions of the letters.
    (Equivalently, when the alphabet has decidable equality, they have the same Parikh
    image.) -/
def CommutativelyEquivalent (α : Type*) (u v : List α) : Prop :=
  Multiset.ofList u = Multiset.ofList v

/-- A series is *commutative* (échangeable) if it takes the same value on all
    commutatively equivalent words. -/
def IsCommutative (α : Type*) (f : Series α) : Prop :=
  ∀ u v, CommutativelyEquivalent α u v → f u = f v

end Lax619925.Series
end

-- Lax619925.Prevariety
section
namespace Lax619925.Prevariety
end Lax619925.Prevariety

namespace Lax619925.Prevariety.EffectivePrevariety
end Lax619925.Prevariety.EffectivePrevariety

namespace Lax619925.Prevariety.Prevariety
end Lax619925.Prevariety.Prevariety
end

-- Lax619925.Commutativity
section
namespace Lax619925.Commutativity

open Lax619925.Series Lax619925.Prevariety

/-- The alphabet `α` extended by two fresh letters `fresh0` and `fresh1`, modelling
    the paper's enlarged alphabet `Γ = Σ ∪ {a, b}`. -/
inductive Fresh2 (α : Type*) where
  | letter : α → Fresh2 α
  | fresh0 : Fresh2 α
  | fresh1 : Fresh2 α

/-- Lift a word over the extended alphabet back to a word over `α`, returning
    `some` of the original word when no fresh letter occurs and `none` otherwise. -/
def liftWordOpt (α : Type*) (w : List (Fresh2 α)) : Option (List α) :=
  match w with
  | [] => some []
  | s :: w' =>
      match s with
      | .letter a => (liftWordOpt α w').map (fun rest => a :: rest)
      | .fresh0 | .fresh1 => none

/-- The extension of a series over `α` to the extended alphabet `Fresh2 α`, by zero
    on words containing one of the two fresh letters. -/
def extendSeries (α : Type*) (f : Series α) : Series (Fresh2 α) := fun w =>
  match liftWordOpt α w with
  | some rest => f rest
  | none => 0

/-- The series `g` over the extended alphabet associated to `f` in the paper's
    equality-reduces-to-commutativity construction: `g` is zero except on words
    beginning with the two fresh letters, where `g (fresh0 :: fresh1 :: rest) = f (rest)`
    (with `f` extended by zero).  Hence `leftDeriv b (leftDeriv a g) = extendSeries f`
    for `a = fresh0`, `b = fresh1`, while every other second left derivative vanishes;
    in particular `g ε = g x = 0` for every letter `x`. -/
def antiDerivativeSeries (α : Type*) (f : Series α) : Series (Fresh2 α) := fun w =>
  match w with
  | .fresh0 :: .fresh1 :: rest => extendSeries α f rest
  | _ => 0

/-- The series `antiDerivativeSeries f` is commutative if and only if `f = 0`
    (paper §3, lemma `equality reduces to commutativity`).  If `f ≠ 0` with
    `f (w) ≠ 0` for some word `w`, then `g (fresh0 · fresh1 · w) = f (w) ≠ 0` while
    `g (fresh1 · fresh0 · w) = 0`, and the two words are commutatively equivalent,
    so `g` is not commutative; conversely `f = 0` forces `g = 0`. -/
axiom AntiDerivativeCommutativeIffZero (α : Type*) (f : Series α) :
  IsCommutative (Fresh2 α) (antiDerivativeSeries α f) ↔ f = 0

end Lax619925.Commutativity
end
