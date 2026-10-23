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
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
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

open FortifiedSquaring

open scoped BigOperators

abbrev History (t : ℕ) (W : Type) := Fin t × (Fin t → W)

end Lax253009.TupleFortification
end

-- Lax253009.CenteredProjection
section
namespace Lax253009.CenteredProjection
end Lax253009.CenteredProjection

namespace Lax253009.CenteredProjection.System
end Lax253009.CenteredProjection.System
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

axiom size_polynomial {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W] (S : Scheme) :
    Fintype.card (S.centers U) + Fintype.card (S.extensions Ω W) + Fintype.card (S.questions W) ≤
      (S.extensionCoefficient + 2) * (Fintype.card U + Fintype.card Ω + Fintype.card W + 1) ^
        (S.centerPower + S.questionPower + S.extensionPower)

end Scheme

end Lax253009.Amplification
end
