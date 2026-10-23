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
end Lax253009.ProjectionGames

namespace Lax253009.ProjectionGames.System
end Lax253009.ProjectionGames.System
end

-- Lax253009.FortifiedSquaring
section
namespace Lax253009.FortifiedSquaring

open FiniteProbability

structure Game (Z W A B : Type) where
  left : Z → W
  right : Z → W
  validLeft : Z → A → Bool
  validRight : Z → A → Bool
  projectLeft : Z → A → B
  projectRight : Z → A → B

namespace Game

variable {Z W A B : Type} (G : Game Z W A B)

def Test (z : Z) (a b : A) : Prop :=
  G.validLeft z a = true ∧ G.validRight z b = true ∧
    G.projectLeft z a = G.projectRight z b

def Wins (P Q : W → A) (z : Z) : Prop := G.Test z (P (G.left z)) (Q (G.right z))

def Sound [Fintype Z] (s : ℝ) : Prop :=
  ∀ P Q : W → A, probability (G.Wins P Q) ≤ s

end Game

end Lax253009.FortifiedSquaring
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

def Sound [Fintype U] [Fintype Ω] (s : ℝ) : Prop :=
  ∀ (P : W → Y) (Q : U → X),
    probability (fun z : U × Ω ↦ G.Test z.1 z.2 (P (G.question z.1 z.2)) (Q z.1)) ≤ s

def symmetrize : Game (U × (Ω × Ω)) W Y X where
  left z := G.question z.1 z.2.1
  right z := G.question z.1 z.2.2
  validLeft z y := G.valid z.1 z.2.1 y
  validRight z y := G.valid z.1 z.2.2 y
  projectLeft z y := G.project z.1 z.2.1 y
  projectRight z y := G.project z.1 z.2.2 y

end System

axiom symmetrize_sound {U Ω W X Y : Type}
    [Fintype U] [Fintype Ω] [Nonempty Ω]
    (G : System U Ω W X Y) (s : ℝ) (h : G.Sound s) : G.symmetrize.Sound s

end Lax253009.CenteredProjection
end
