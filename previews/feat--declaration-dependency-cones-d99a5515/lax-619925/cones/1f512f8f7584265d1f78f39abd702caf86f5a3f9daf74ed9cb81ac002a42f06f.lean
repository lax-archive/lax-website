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
namespace Lax619925.Commutativity.antiDerivativeSeries
end Lax619925.Commutativity.antiDerivativeSeries

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

end Lax619925.Commutativity
end
