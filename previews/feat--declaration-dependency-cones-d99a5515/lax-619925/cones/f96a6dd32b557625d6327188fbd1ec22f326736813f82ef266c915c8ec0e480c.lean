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
import Mathlib.Data.Nat.Choose.Basic
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
namespace Lax619925.Shuffle
end Lax619925.Shuffle

namespace Lax619925.Shuffle.ShuffleAutomaton
end Lax619925.Shuffle.ShuffleAutomaton

namespace Lax619925.Shuffle.shufflePow
end Lax619925.Shuffle.shufflePow

namespace Lax619925.Shuffle.shuffleRec
end Lax619925.Shuffle.shuffleRec
end

-- Lax619925.CDA
section
namespace Lax619925.CDA

open Lax619925.Series Lax619925.Shuffle

/-- An exponential multivariate power series in `d` variables, identified with
    its coefficient sequence (the series is `Σ_n f_n x^n / n!`). -/
abbrev ExpPowerSeries (d : ℕ) := (Fin d → ℕ) → ℚ

/-- The binomial-convolution product of two exponential power series:
    `(expMul d f g) n = Σ_{m ≤ n} binom(n, m) f m · g (n - m)`, the product in the
    exponential (binomial) algebra, where the sum is over the multi-indices
    `m ≤ n` (coordinate-wise) and `binom(n, m) = ∏_i binom(n_i, m_i)` is the
    multinomial coefficient. -/
noncomputable def expMul (d : ℕ) (f g : ExpPowerSeries d) : ExpPowerSeries d :=
  fun n =>
    (Finset.univ.pi (fun i => Finset.range (n i + 1))).sum fun m =>
      let m' : Fin d → ℕ := fun i => m i (Finset.mem_univ i)
      (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n i) (m' i)) * f m' * g (fun i => n i - m' i)

/-- The `n`-fold binomial-convolution power of an exponential power series:
    `expPow d f 0` is the constant-1 series and `expPow d f (n+1) = expMul d (expPow d f n) f`. -/
noncomputable def expPow (d : ℕ) (f : ExpPowerSeries d) (n : ℕ) : ExpPowerSeries d :=
  match n with
  | 0 => fun idx => if idx = 0 then 1 else 0
  | n + 1 => expMul d (expPow d f n) f

/-- The evaluation of the polynomial `p` at the tuple of exponential power series
    `fs`, in the binomial-convolution algebra: the variable `X_i` is mapped to
    `fs i` and the multiplication is the binomial-convolution product. -/
noncomputable def evalCDA (d k : ℕ) (fs : Fin k → ExpPowerSeries d) (p : MvPolynomial (Fin k) ℚ) :
    ExpPowerSeries d :=
  p.support.sum fun m =>
    p.coeff m • (Finset.univ : Finset (Fin k)).toList.foldr
      (fun i acc => expMul d acc (expPow d (fs i) (m i)))
      (fun idx => if idx = 0 then 1 else 0)

end Lax619925.CDA
end
