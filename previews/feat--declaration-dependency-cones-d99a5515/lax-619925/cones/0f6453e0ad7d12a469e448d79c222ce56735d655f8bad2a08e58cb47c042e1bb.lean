-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic

-- Lax619925.Series
section
namespace Lax619925
end Lax619925

namespace Lax619925.Series
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

-- Lax619925.Hadamard
section
namespace Lax619925.Hadamard
end Lax619925.Hadamard

namespace Lax619925.Hadamard.HadamardAutomaton
end Lax619925.Hadamard.HadamardAutomaton
end

-- Lax619925.PolynomialAutomata
section
namespace Lax619925.PolynomialAutomata

open Lax619925.Series Lax619925.Hadamard

/-- A *polynomial automaton* over `α`: a dimension `k ≥ 1`, an initial
    configuration `qI : ℚ^k`, a final polynomial `F : ℚ[X_1, …, X_k]`, and a
    transition `Δ` assigning to each letter `a` a polynomial map
    `Δ_a : ℚ^k → ℚ^k` (a `k`-tuple of polynomials).  The configuration space is
    the vector space `ℚ^k`, and the letter action is `q · a = Δ_a(q)` (evaluate
    the transition polynomials at the point `q`). -/
structure PolynomialAutomaton (α : Type*) where
  dim : ℕ
  hdim : 0 < dim
  qI : Fin dim → ℚ
  F : MvPolynomial (Fin dim) ℚ
  Δ : α → Fin dim → MvPolynomial (Fin dim) ℚ

end Lax619925.PolynomialAutomata
end
