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
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
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

open FortifiedSquaring

open scoped BigOperators

abbrev History (t : ℕ) (W : Type) := Fin t × (Fin t → W)

def plant {W : Type} {t : ℕ} (w : W) (h : History t W) : Fin t → W :=
  Function.update h.2 h.1 w

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

def fortify (t : ℕ) : System U (Ω × History t W) (Fin t → W) X (Fin t → Y) where
  question u ω := plant (G.question u ω.1) ω.2
  valid u ω y := G.valid u ω.1 (y ω.2.1)
  project u ω y := G.project u ω.1 (y ω.2.1)

def tensor : System (U × U) (Ω × Ω) (W × W) (X × X) (Y × Y) where
  question u ω := (G.question u.1 ω.1, G.question u.2 ω.2)
  valid u ω y := G.valid u.1 ω.1 y.1 && G.valid u.2 ω.2 y.2
  project u ω y := (G.project u.1 ω.1 y.1, G.project u.2 ω.2 y.2)

end System

end Lax323828.CenteredProjection
end

-- Lax323828.Amplification
section
namespace Lax323828.Amplification.Scheme.centersNonempty
end Lax323828.Amplification.Scheme.centersNonempty

namespace Lax323828.Amplification

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

def transform {U Ω W X Y : Type} (S : Scheme) (G : System U Ω W X Y) :
    System (centers S U) (extensions S Ω W) (questions S W) (centers S X) (questions S Y) :=
  match S with
  | .base => G
  | .step t S => ((transform S G).fortify t).tensor

end Scheme

end Lax323828.Amplification
end
