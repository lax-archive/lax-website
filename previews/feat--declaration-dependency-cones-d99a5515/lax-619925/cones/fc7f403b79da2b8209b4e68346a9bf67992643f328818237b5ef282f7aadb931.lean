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

-- Lax619925.Polyrec
section
namespace Lax619925.Polyrec

open Lax619925.Series Lax619925.Hadamard

/-- A multivariate sequence in `d` variables: a function `ℕ^d → ℚ`, represented
    as a function on the multi-index type `Fin d → ℕ`. -/
abbrev Seq (d : ℕ) := (Fin d → ℕ) → ℚ

/-- The shift of a multivariate sequence in the `j`-th coordinate:
    `(shift d j f) n = f (n + e_j)`, where `e_j` is the `j`-th unit vector.
    The shifts in different coordinates commute. -/
def shift (d : ℕ) (j : Fin d) (f : Seq d) : Seq d :=
  fun n => f (fun i => n i + if i = j then 1 else 0)

/-- The pointwise (Hadamard-algebra) evaluation of the polynomial `p` at the tuple
    of sequences `fs`: `evalSeq d k fs p n = Σ_m p.coeff m · ∏_i (fs i n)^{m i}`,
    the interpretation of `p` in the pointwise ring of sequences, where the
    variable `X_i` is mapped to `fs i` and the multiplication is pointwise. -/
def evalSeq (d k : ℕ) (fs : Fin k → Seq d) (p : MvPolynomial (Fin k) ℚ) : Seq d :=
  fun n => p.support.sum fun m => p.coeff m * ∏ i : Fin k, (fs i) n ^ (m i)

/-- A `k`-tuple of multivariate sequences `f` *solves* the polyrec system
    `(p, c)` if it satisfies the initial condition `f_i(0) = c_i` and the
    polynomial equations `shift_j f_i = p^{(j)}_i(f_1, …, f_k)` for all `i, j`,
    where `p^{(j)}_i` is evaluated pointwise in the sequences (the Hadamard
    algebra).  Here `0` is the zero multi-index, the origin of `ℕ^d`. -/
def SolvesPolyrec (d k : ℕ) (f : Fin k → Seq d)
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ) : Prop :=
  (∀ i, f i 0 = c i) ∧ ∀ i j, shift d j (f i) = evalSeq d k f (p i j)

/-- The polyrec consistency problem is decidable (paper §5.4, theorem
    `polyrec consistency`): there is a procedure that, given the polynomial
    equations `p` and the initial condition `c`, decides whether a solution
    exists.  The decision reduces to the commutativity of the companion Hadamard
    series, which is decidable. -/
axiom PolyrecConsistency (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
  ∃ dec : (Fin k → Fin d → MvPolynomial (Fin k) ℚ) → (Fin k → ℚ) → Bool,
    ∀ p c, dec p c = true ↔ ∃ f : Fin k → Seq d, SolvesPolyrec d k f p c

end Lax619925.Polyrec
end
