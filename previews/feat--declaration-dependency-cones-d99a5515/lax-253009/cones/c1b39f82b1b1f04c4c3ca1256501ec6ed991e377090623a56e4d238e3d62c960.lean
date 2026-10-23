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

open FortifiedSquaring

open scoped BigOperators

abbrev History (t : ℕ) (W : Type) := Fin t × (Fin t → W)

def plant {W : Type} {t : ℕ} (w : W) (h : History t W) : Fin t → W :=
  Function.update h.2 h.1 w

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

def Uniform [Fintype U] [Fintype Ω] [Fintype W] : Prop :=
  ∀ f : W → ℝ, (𝔼 u, 𝔼 ω, f (G.question u ω)) = 𝔼 w, f w

def symmetrize : Game (U × (Ω × Ω)) W Y X where
  left z := G.question z.1 z.2.1
  right z := G.question z.1 z.2.2
  validLeft z y := G.valid z.1 z.2.1 y
  validRight z y := G.valid z.1 z.2.2 y
  projectLeft z y := G.project z.1 z.2.1 y
  projectRight z y := G.project z.1 z.2.2 y

def fortify (t : ℕ) : System U (Ω × History t W) (Fin t → W) X (Fin t → Y) where
  question u ω := plant (G.question u ω.1) ω.2
  valid u ω y := G.valid u ω.1 (y ω.2.1)
  project u ω y := G.project u ω.1 (y ω.2.1)

def tensor : System (U × U) (Ω × Ω) (W × W) (X × X) (Y × Y) where
  question u ω := (G.question u.1 ω.1, G.question u.2 ω.2)
  valid u ω y := G.valid u.1 ω.1 y.1 && G.valid u.2 ω.2 y.2
  project u ω y := (G.project u.1 ω.1 y.1, G.project u.2 ω.2 y.2)

end System

end Lax253009.CenteredProjection
end

-- Lax253009.Amplification
section
namespace Lax253009.Amplification.Scheme.centersNonempty
end Lax253009.Amplification.Scheme.centersNonempty

namespace Lax253009.Amplification

open CenteredProjection TupleFortification

open scoped BigOperators

inductive Scheme where
  | base
  | step (t : ℕ+) (previous : Scheme)

namespace Scheme

def centers (S : Scheme) (U : Type) : Type := match S with
  | .base => U
  | .step _ S => centers S U × centers S U

def questions (S : Scheme) (W : Type) : Type := match S with
  | .base => W
  | .step t S => (Fin t → questions S W) × (Fin t → questions S W)

def extensions (S : Scheme) (Ω W : Type) : Type := match S with
  | .base => Ω
  | .step t S => (extensions S Ω W × History t (questions S W)) ×
      (extensions S Ω W × History t (questions S W))

instance centersFintype {U : Type} [Fintype U] (S : Scheme) : Fintype (centers S U) :=
  match S with
  | .base => inferInstanceAs (Fintype U)
  | .step _ S =>
    letI : Fintype (centers S U) := centersFintype S
    inferInstanceAs (Fintype (centers S U × centers S U))

instance questionsFintype {W : Type} [Fintype W] (S : Scheme) : Fintype (questions S W) :=
  match S with
  | .base => inferInstanceAs (Fintype W)
  | .step t S =>
    letI : Fintype (questions S W) := questionsFintype S
    inferInstanceAs (Fintype ((Fin t → questions S W) × (Fin t → questions S W)))

instance extensionsFintype {Ω W : Type} [Fintype Ω] [Fintype W] (S : Scheme) :
    Fintype (extensions S Ω W) := match S with
  | .base => inferInstanceAs (Fintype Ω)
  | .step t S =>
    letI : Fintype (extensions S Ω W) := extensionsFintype S
    inferInstanceAs (Fintype ((extensions S Ω W × History t (questions S W)) ×
      (extensions S Ω W × History t (questions S W))))

def transform {U Ω W X Y : Type} (S : Scheme) (G : System U Ω W X Y) :
    System (centers S U) (extensions S Ω W) (questions S W) (centers S X) (questions S Y) :=
  match S with
  | .base => G
  | .step t S => ((transform S G).fortify t).tensor

end Scheme

def SoundReduction (S : Scheme) (X Y : Type) [Fintype X] [Fintype Y] (s δ : ℝ) : Prop :=
  ∀ (U Ω W : Type) [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
    [Fintype W] [Nonempty W] (G : System U Ω W X Y),
    G.Uniform → G.symmetrize.Sound s → (S.transform G).symmetrize.Sound δ

axiom exists_small_value_scheme (X Y : Type) [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (s δ : ℝ) (hs : 0 < s) (hs1 : s < 1) (hδ : 0 < δ) :
    ∃ S : Scheme, SoundReduction S X Y s δ

end Lax253009.Amplification
end
