-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Computability.TuringMachine.Computable
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
end Lax253009.GapSatisfiability
end

-- Lax253009.SmallValueSatisfiability
section
namespace Lax253009.SmallValueSatisfiability
end Lax253009.SmallValueSatisfiability
end

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}

end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair

namespace Lax434930.Certificates

open PolynomialTime

/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y

end Lax434930.Certificates
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime

open PolynomialTime Certificates

/-- Languages with polynomially bounded, polynomial-time verifiable certificates. -/
def NP : Set Language :=
  {A | ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V}

end Lax434930.NondeterministicPolynomialTime
end

-- Lax253009.SmallValueNP
section
namespace Lax253009.SmallValueNP

open CenteredProjection

axiom reduction (δ : ℝ) (hδ : 0 < δ) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
      ∀ L ∈ Lax434930.NondeterministicPolynomialTime.NP, ∃ K e : ℕ,
        ∀ z : List Bool,
          ∃ u o w : ℕ, 0 < u ∧ 0 < o ∧ 0 < w ∧ u + o + w ≤ K * (z.length + 1) ^ e ∧
            ∃ G : System (Fin u) (Fin o) (Fin w) (Fin x) (Fin y),
              (z ∈ L → G.Complete) ∧ (z ∉ L → G.Sound δ)

end Lax253009.SmallValueNP
end
