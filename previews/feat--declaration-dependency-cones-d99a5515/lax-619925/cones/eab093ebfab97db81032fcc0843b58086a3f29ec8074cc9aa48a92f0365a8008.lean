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

-- Lax619925.Hadamard
section
namespace Lax619925.Hadamard

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- A *Hadamard automaton* over `α`: a dimension `k ≥ 1` (the number of
    nonterminals `X_1, …, X_k`), a final-weight functional `F`, and a transition
    `Δ` assigning to each letter `a` and nonterminal `X_i` a polynomial `Δ a i` in
    the nonterminals.  The configuration space is the polynomial ring
    `ℚ[X_1, …, X_k] = MvPolynomial (Fin k) ℚ`. -/
structure HadamardAutomaton (α : Type*) where
  dim : ℕ
  hdim : 0 < dim
  F : Fin dim → ℚ
  Δ : α → Fin dim → MvPolynomial (Fin dim) ℚ

/-- The word extension of the transition: `Δ_w` is the endomorphism of the
    configuration space obtained by composing the letter endomorphisms
    `aeval (Δ a)` along the word, right-to-left.  `Δ_ε` is the identity and
    `Δ_{a·w} = Δ_w ∘ Δ_a`. -/
noncomputable def HadamardAutomaton.Mword {α : Type*} (A : HadamardAutomaton α) (w : List α) :
    MvPolynomial (Fin A.dim) ℚ → MvPolynomial (Fin A.dim) ℚ :=
  w.foldr (fun a φ => fun β => φ (MvPolynomial.aeval (A.Δ a) β)) id

/-- The series recognised by the automaton at a configuration `cfg`:
    `⟦A⟧_cfg (w) = F(Δ_w cfg)`, the final-weight functional applied to the
    configuration reached after reading `w`. -/
noncomputable def HadamardAutomaton.sem {α : Type*} (A : HadamardAutomaton α)
    (cfg : MvPolynomial (Fin A.dim) ℚ) : Series α :=
  fun w => MvPolynomial.eval (fun i => A.F i) (A.Mword w cfg)

/-- The series recognised by the automaton: the semantics at the initial
    configuration `X_0` (the first nonterminal). -/
noncomputable def HadamardAutomaton.recognised {α : Type*} (A : HadamardAutomaton α) :
    Series α :=
  A.sem (MvPolynomial.X (Fin.mk 0 A.hdim))

/-- In particular, the commutativity problem is decidable for Hadamard-finite series
    over a finite alphabet (paper §5): there is a procedure that, given a Hadamard
    automaton, decides whether the series it recognises is commutative.  This is the
    meta-theorem applied to the effective prevariety of Hadamard-finite series. -/
axiom HadamardCommutativityDecidable (α : Type*) [Fintype α] :
  ∃ d : HadamardAutomaton α → Bool, ∀ A, d A = true ↔ IsCommutative α (A.recognised)

end Lax619925.Hadamard
end
