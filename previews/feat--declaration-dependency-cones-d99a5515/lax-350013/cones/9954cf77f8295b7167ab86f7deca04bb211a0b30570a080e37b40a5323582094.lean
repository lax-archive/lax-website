-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

-- Lax350013.MatrixParameters
section
namespace Lax350013.MatrixParameters

open Finset

/-- Section 2.4.3: "α_d := binom(m, d) 9^d". -/
def alpha (m d : ℕ) : ℕ := m.choose d * 9 ^ d

/-- The expression inside the `O(·)` of the query time of Theorem 30:
"L ∑_{d=0}^{t} α_d". -/
noncomputable def costQuery (L m t : ℕ) : ℝ := (L : ℝ) * ∑ d ∈ range (t + 1), (alpha m d : ℝ)

end Lax350013.MatrixParameters
end
