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

end Lax323828.TupleFortification
end

-- Lax323828.CenteredProjection
section
namespace Lax323828.CenteredProjection
end Lax323828.CenteredProjection

namespace Lax323828.CenteredProjection.System
end Lax323828.CenteredProjection.System
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

def centerPower : Scheme → ℕ
  | .base => 1
  | .step _ S => S.centerPower * 2

def questionPower : Scheme → ℕ
  | .base => 1
  | .step t S => S.questionPower * t * 2

def extensionCoefficient : Scheme → ℕ
  | .base => 1
  | .step t S => (S.extensionCoefficient * t) ^ 2

def extensionPower : Scheme → ℕ
  | .base => 0
  | .step t S => (S.extensionPower + S.questionPower * t) * 2

axiom card_extensions {Ω W : Type} [Fintype Ω] [Fintype W] (S : Scheme) :
    Fintype.card (S.extensions Ω W) =
      S.extensionCoefficient * Fintype.card Ω ^ S.centerPower * Fintype.card W ^ S.extensionPower

end Scheme

end Lax323828.Amplification
end
