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

/-- The action of a letter `a` on a configuration `q`: `q · a = Δ_a(q)`,
    evaluate the transition polynomials at the point `q`. -/
noncomputable def PolynomialAutomaton.action {α : Type*} (A : PolynomialAutomaton α)
    (q : Fin A.dim → ℚ) (a : α) : Fin A.dim → ℚ :=
  fun i => MvPolynomial.eval q (A.Δ a i)

/-- The action of a word `w` on a configuration `q`: `q · w`, the letter actions
    iterated left-to-right. -/
noncomputable def PolynomialAutomaton.wordAction {α : Type*} (A : PolynomialAutomaton α)
    (q : Fin A.dim → ℚ) (w : List α) : Fin A.dim → ℚ :=
  w.foldl (fun q a => A.action q a) q

/-- The series recognised by the automaton at a configuration `q`:
    `⟦A⟧_q (w) = F(q · w)`, the final polynomial `F` evaluated at the point
    `q · w` reached after reading `w`. -/
noncomputable def PolynomialAutomaton.sem {α : Type*} (A : PolynomialAutomaton α)
    (q : Fin A.dim → ℚ) : Series α :=
  fun w => MvPolynomial.eval (A.wordAction q w) A.F

/-- The series recognised by the automaton: the semantics at the initial
    configuration `qI`. -/
noncomputable def PolynomialAutomaton.recognised {α : Type*} (A : PolynomialAutomaton α) : Series α :=
  A.sem A.qI

/-- A series is *polynomial-recognisable* if it is recognised by some polynomial
    automaton. -/
def IsPolynomialRecognisable (α : Type*) (f : Series α) : Prop :=
  ∃ A : PolynomialAutomaton α, A.recognised = f

end Lax619925.PolynomialAutomata
end
