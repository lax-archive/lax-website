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

-- Lax619925.Shuffle
section
namespace Lax619925.Shuffle.ShuffleAutomaton
end Lax619925.Shuffle.ShuffleAutomaton

namespace Lax619925.Shuffle.shufflePow
end Lax619925.Shuffle.shufflePow

namespace Lax619925.Shuffle.shuffleRec
end Lax619925.Shuffle.shuffleRec

namespace Lax619925.Shuffle

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- The unique derivation of the polynomial ring `MvPolynomial σ R` sending the
    variable `X i` to `φ i`, defined by the Leibniz rule on monomials:
    `δ_φ(X^m) = Σ_i m_i · X^{m - e_i} · φ i`.  This is the extension of the
    letter transition `Δ_a` (a map on the variables) to a derivation of the whole
    configuration space. -/
noncomputable def derivationExt {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) : MvPolynomial σ R → MvPolynomial σ R :=
  fun p => p.support.sum fun m =>
    p.coeff m • (∑ i : σ, ((m i : R) • MvPolynomial.monomial (m - Finsupp.single i 1) 1) * φ i)

end Lax619925.Shuffle
end
