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

def Test (v : V) (ω : D × Bool) (p : A × A) (a : A) : Prop :=
  C.relation (C.question v ω) p.1 p.2 = true ∧ project ω.2 p = a

def Violated (a : V → A) (z : V × D) : Prop :=
  C.relation z (a z.1) (a (C.reverse z).1) ≠ true

def Satisfiable : Prop := ∃ a : V → A, ∀ z, ¬ C.Violated a z

end System

axiom completeness {V D A : Type} (C : System V D A) (h : C.Satisfiable) :
  ∃ P : V × D → A × A, ∃ Q : V → A,
    ∀ v ω, C.Test v ω (P (C.question v ω)) (Q v)

end Lax253009.ProjectionGames
end
