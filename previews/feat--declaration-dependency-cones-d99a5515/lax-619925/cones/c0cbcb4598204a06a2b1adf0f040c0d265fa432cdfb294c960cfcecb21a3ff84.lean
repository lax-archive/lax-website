-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Basic
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

-- Lax619925.Infiltration
section
namespace Lax619925.Infiltration.infiltrationPow
end Lax619925.Infiltration.infiltrationPow

namespace Lax619925.Infiltration.infiltrationRec
end Lax619925.Infiltration.infiltrationRec

namespace Lax619925.Infiltration

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- An *infiltration automaton* over `α`: a dimension `k ≥ 1` (the number of
    nonterminals `X_1, …, X_k`), a final-weight functional `F`, and a transition
    `Δ` assigning to each letter `a` and nonterminal `X_i` a polynomial `Δ a i` in
    the nonterminals.  The configuration space is the polynomial ring
    `ℚ[X_1, …, X_k] = MvPolynomial (Fin k) ℚ`. -/
structure InfiltrationAutomaton (α : Type*) where
  dim : ℕ
  hdim : 0 < dim
  F : Fin dim → ℚ
  Δ : α → Fin dim → MvPolynomial (Fin dim) ℚ

end Lax619925.Infiltration
end
