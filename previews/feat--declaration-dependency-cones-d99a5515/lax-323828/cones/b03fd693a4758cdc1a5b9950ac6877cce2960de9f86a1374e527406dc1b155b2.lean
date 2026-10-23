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

-- Lax323828.FiniteProbability
section
namespace Lax323828.FiniteProbability

open scoped Classical

open scoped BigOperators

/-- The proportion of points in the finite sample space satisfying the event `P`. -/
noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax323828.FiniteProbability
end

-- Lax323828.DecodedStrategies
section
namespace Lax323828.DecodedStrategies
end Lax323828.DecodedStrategies
end

-- Lax323828.ProjectionGames
section
namespace Lax323828.ProjectionGames
end Lax323828.ProjectionGames

namespace Lax323828.ProjectionGames.System
end Lax323828.ProjectionGames.System
end

-- Lax323828.FortifiedSquaring
section
namespace Lax323828.FortifiedSquaring
end Lax323828.FortifiedSquaring

namespace Lax323828.FortifiedSquaring.Game
end Lax323828.FortifiedSquaring.Game
end

-- Lax323828.TupleFortification
section
namespace Lax323828.TupleFortification
end Lax323828.TupleFortification
end

-- Lax323828.CenteredProjection
section
namespace Lax323828.CenteredProjection

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

end Lax323828.CenteredProjection
end

-- Lax323828.Amplification
section
namespace Lax323828.Amplification
end Lax323828.Amplification

namespace Lax323828.Amplification.Scheme
end Lax323828.Amplification.Scheme

namespace Lax323828.Amplification.Scheme.base
end Lax323828.Amplification.Scheme.base

namespace Lax323828.Amplification.Scheme.centers
end Lax323828.Amplification.Scheme.centers

namespace Lax323828.Amplification.Scheme.centersNonempty
end Lax323828.Amplification.Scheme.centersNonempty

namespace Lax323828.Amplification.Scheme.step
end Lax323828.Amplification.Scheme.step
end

-- Lax323828.GapSatisfiability
section
namespace Lax323828.GapSatisfiability

abbrev Literal := Bool × ℕ

abbrev Formula := List (List Literal)

def Is3CNF (φ : Formula) : Prop := ∀ c ∈ φ, c.length = 3

def Satisfiable (φ : Formula) : Prop :=
  ∃ a : List Bool, ∀ c ∈ φ, ∃ l ∈ c, (a[l.2]?).getD false = l.1

end Lax323828.GapSatisfiability
end

-- Lax323828.SmallValueSatisfiability
section
namespace Lax323828.SmallValueSatisfiability

open CenteredProjection GapSatisfiability

axiom reduction (δ : ℝ) (hδ : 0 < δ) :
    ∃ x y K e : ℕ, 0 < x ∧ 0 < y ∧
      ∀ φ : Formula, Is3CNF φ →
        ∃ u o w : ℕ, 0 < u ∧ 0 < o ∧ 0 < w ∧ u + o + w ≤ K * (φ.length + 1) ^ e ∧
          ∃ G : System (Fin u) (Fin o) (Fin w) (Fin x) (Fin y),
            (Satisfiable φ → G.Complete) ∧ (¬ Satisfiable φ → G.Sound δ)

end Lax323828.SmallValueSatisfiability
end
