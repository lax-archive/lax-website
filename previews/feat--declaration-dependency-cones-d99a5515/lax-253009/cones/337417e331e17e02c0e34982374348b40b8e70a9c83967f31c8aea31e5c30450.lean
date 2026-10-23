-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.PNat.Basic
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
end Lax253009.ProjectionGames

namespace Lax253009.ProjectionGames.System
end Lax253009.ProjectionGames.System
end

-- Lax253009.FortifiedSquaring
section
namespace Lax253009.FortifiedSquaring
end Lax253009.FortifiedSquaring

namespace Lax253009.FortifiedSquaring.Game
end Lax253009.FortifiedSquaring.Game
end

-- Lax253009.TupleFortification
section
namespace Lax253009.TupleFortification
end Lax253009.TupleFortification
end

-- Lax253009.CenteredProjection
section
namespace Lax253009.CenteredProjection

open FiniteProbability FortifiedSquaring TupleFortification

open scoped BigOperators

structure System (U Ω W X Y : Type) where
  question : U → Ω → W
  valid : U → Ω → Y → Bool
  project : U → Ω → Y → X

namespace System

variable {U Ω W X Y : Type} (G : System U Ω W X Y)

def Test (u : U) (ω : Ω) (y : Y) (x : X) : Prop :=
  G.valid u ω y = true ∧ G.project u ω y = x

def Complete : Prop := ∃ P : W → Y, ∃ Q : U → X,
  ∀ u ω, G.Test u ω (P (G.question u ω)) (Q u)

def Sound [Fintype U] [Fintype Ω] (s : ℝ) : Prop :=
  ∀ (P : W → Y) (Q : U → X),
    probability (fun z : U × Ω ↦ G.Test z.1 z.2 (P (G.question z.1 z.2)) (Q z.1)) ≤ s

end System

end Lax253009.CenteredProjection
end

-- Lax253009.Amplification
section
namespace Lax253009.Amplification
end Lax253009.Amplification

namespace Lax253009.Amplification.Scheme
end Lax253009.Amplification.Scheme

namespace Lax253009.Amplification.Scheme.base
end Lax253009.Amplification.Scheme.base

namespace Lax253009.Amplification.Scheme.centers
end Lax253009.Amplification.Scheme.centers

namespace Lax253009.Amplification.Scheme.centersNonempty
end Lax253009.Amplification.Scheme.centersNonempty

namespace Lax253009.Amplification.Scheme.step
end Lax253009.Amplification.Scheme.step
end

-- Lax253009.GapSatisfiability
section
namespace Lax253009.GapSatisfiability

abbrev Literal := Bool × ℕ

abbrev Formula := List (List Literal)

def Is3CNF (φ : Formula) : Prop := ∀ c ∈ φ, c.length = 3

def Satisfiable (φ : Formula) : Prop :=
  ∃ a : List Bool, ∀ c ∈ φ, ∃ l ∈ c, (a[l.2]?).getD false = l.1

end Lax253009.GapSatisfiability
end

-- Lax253009.SmallValueSatisfiability
section
namespace Lax253009.SmallValueSatisfiability

open CenteredProjection GapSatisfiability

axiom reduction (δ : ℝ) (hδ : 0 < δ) :
    ∃ x y K e : ℕ, 0 < x ∧ 0 < y ∧
      ∀ φ : Formula, Is3CNF φ →
        ∃ u o w : ℕ, 0 < u ∧ 0 < o ∧ 0 < w ∧ u + o + w ≤ K * (φ.length + 1) ^ e ∧
          ∃ G : System (Fin u) (Fin o) (Fin w) (Fin x) (Fin y),
            (Satisfiable φ → G.Complete) ∧ (¬ Satisfiable φ → G.Sound δ)

end Lax253009.SmallValueSatisfiability
end
