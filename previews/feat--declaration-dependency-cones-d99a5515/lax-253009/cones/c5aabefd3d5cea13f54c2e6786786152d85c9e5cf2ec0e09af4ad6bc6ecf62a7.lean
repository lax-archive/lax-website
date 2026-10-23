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

open FiniteProbability

structure System (V D A : Type) where
  reverse : V × D → V × D
  reverse_involutive : Function.Involutive reverse
  relation : V × D → A → A → Bool

namespace System

variable {V D A : Type} (C : System V D A)

def question (v : V) (ω : D × Bool) : V × D :=
  if ω.2 then C.reverse (v, ω.1) else (v, ω.1)

def project (b : Bool) (p : A × A) : A := if b then p.2 else p.1

end System

end Lax253009.ProjectionGames
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

def Uniform [Fintype U] [Fintype Ω] [Fintype W] : Prop :=
  ∀ f : W → ℝ, (𝔼 u, 𝔼 ω, f (G.question u ω)) = 𝔼 w, f w

end System

def fromConstraints {V D A : Type} (C : ProjectionGames.System V D A) :
    System V (D × Bool) (V × D) A (A × A) where
  question := C.question
  valid v ω p := C.relation (C.question v ω) p.1 p.2
  project _ ω p := ProjectionGames.System.project ω.2 p

axiom from_constraints_uniform {V D A : Type} [Fintype V] [Fintype D]
    (C : ProjectionGames.System V D A) : (fromConstraints C).Uniform

end Lax253009.CenteredProjection
end
