-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009.FiniteProbability

open scoped BigOperators

noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax253009.FiniteProbability
end

-- Lax253009.DecodedStrategies
section
namespace Lax253009.DecodedStrategies
end Lax253009.DecodedStrategies
end

-- Lax253009.ProjectionGames
section
namespace Lax253009.ProjectionGames

open FiniteProbability

structure System (V D A : Type) where
  reverse : V × D → V × D
  reverse_involutive : Function.Involutive reverse
  relation : V × D → A → A → Bool

namespace System

variable {V D A : Type} (C : System V D A)

def Violated (a : V → A) (z : V × D) : Prop :=
  C.relation z (a z.1) (a (C.reverse z).1) ≠ true

def Satisfiable : Prop := ∃ a : V → A, ∀ z, ¬ C.Violated a z

def Sound [Fintype V] [Fintype D] (γ : ℝ) : Prop :=
  ∀ a : V → A, γ ≤ probability (C.Violated a)

end System

end Lax253009.ProjectionGames
end

-- Lax253009.GapSatisfiability
section
namespace Lax253009.GapSatisfiability

abbrev Literal := Bool × ℕ

abbrev Formula := List (List Literal)

def Is3CNF (φ : Formula) : Prop := ∀ c ∈ φ, c.length = 3

def Satisfiable (φ : Formula) : Prop :=
  ∃ a : List Bool, ∀ c ∈ φ, ∃ l ∈ c, (a[l.2]?).getD false = l.1

axiom regular_gap :
  ∃ a d K e : ℕ, 0 < a ∧ 0 < d ∧ 0 < K ∧
    ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : Formula, Is3CNF φ →
        ∃ n : ℕ, 0 < n ∧ n ≤ K * (φ.length + 1) ^ e ∧
          ∃ C : ProjectionGames.System (Fin n) (Fin d) (Fin a),
            (Satisfiable φ → C.Satisfiable) ∧ (¬ Satisfiable φ → C.Sound γ)

end Lax253009.GapSatisfiability
end
