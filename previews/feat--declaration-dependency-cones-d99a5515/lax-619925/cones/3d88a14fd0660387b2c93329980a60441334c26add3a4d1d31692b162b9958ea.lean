-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Basic

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
end Lax619925.Commutativity

namespace Lax619925.Commutativity.Fresh2
end Lax619925.Commutativity.Fresh2

namespace Lax619925.Commutativity.antiDerivativeSeries
end Lax619925.Commutativity.antiDerivativeSeries

namespace Lax619925.Commutativity.extendSeries
end Lax619925.Commutativity.extendSeries

namespace Lax619925.Commutativity.liftWordOpt
end Lax619925.Commutativity.liftWordOpt

namespace Lax619925.Commutativity.Fresh2.fresh0
end Lax619925.Commutativity.Fresh2.fresh0

namespace Lax619925.Commutativity.Fresh2.fresh1
end Lax619925.Commutativity.Fresh2.fresh1

namespace Lax619925.Commutativity.Fresh2.letter
end Lax619925.Commutativity.Fresh2.letter
end

-- Lax619925.Recognisable
section
namespace Lax619925.Recognisable

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- A linear representation over `α`: a dimension `k`, a row vector `init` of
    initial weights, a column vector `final` of final weights, and a transition
    function `M` assigning to each letter a `k × k` matrix.  The transition function
    extends homomorphically to words by `M(ε) = 1` and `M(a·w) = M(a) · M(w)` (the
    definition `Mword`), and the series recognised is `f (w) = x · M(w) · y` (the
    definition `sem`).  Both are computed from the four core fields. -/
structure LinearRepresentation (α : Type*) where
  dim : ℕ
  init : Fin dim → ℚ
  final : Fin dim → ℚ
  M : α → Matrix (Fin dim) (Fin dim) ℚ

/-- The word product `M(w)`: `M(ε) = 1` and `M(a·w) = M(a) · M(w)`, the transition
    matrices composed right-to-left along the word. -/
def LinearRepresentation.Mword {α : Type*} (r : LinearRepresentation α) (w : List α) :
    Matrix (Fin r.dim) (Fin r.dim) ℚ :=
  w.foldr (fun a A => r.M a * A) 1

/-- The series recognised by the representation: `f (w) = x · M(w) · y`, the dot
    product of the initial vector with the word product applied to the final vector. -/
def LinearRepresentation.sem {α : Type*} (r : LinearRepresentation α) (w : List α) : ℚ :=
  dotProduct r.init (Matrix.mulVec (r.Mword w) r.final)

/-- In particular, the commutativity problem is decidable for recognisable series over
    a finite alphabet (paper §4): there is a procedure that, given a linear
    representation, decides whether the series it recognises is commutative.  This is
    the meta-theorem applied to the effective prevariety of recognisable series. -/
axiom RecognisableCommutativityDecidable (α : Type*) [Fintype α] :
  ∃ d : LinearRepresentation α → Bool, ∀ r, d r = true ↔ IsCommutative α (r.sem)

end Lax619925.Recognisable
end
