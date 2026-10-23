-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.LongCode
section
namespace Lax253009.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

abbrev Table (w : ℕ) := Coordinate w → Bool

def compose {w s : ℕ} (f : Fin s → Coordinate w) (B : Word s → Bool) : Coordinate w :=
  fun x ↦ B (fun i ↦ f i x)

def Accepts {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w) : Prop :=
  ∀ B : Word s → Bool, A (compose f B) = B (fun i ↦ A (f i))

def AgreesOn {w : ℕ} (h g g' : Coordinate w) : Prop :=
  ∀ x, h x = true → g x = g' x

def Queried {w s : ℕ} (f : Fin s → Coordinate w) (g : Coordinate w) : Prop :=
  (∃ i, g = f i) ∨ ∃ B : Word s → Bool, g = compose f B

def AcceptsWithCondition {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) : Prop :=
  Accepts A f ∧ ∀ g, Queried f g → ∀ g', AgreesOn h g g' → A g = A g'

end Lax253009.LongCode
end

-- Lax253009.CNASoundness
section
namespace Lax253009.CNASoundness
end Lax253009.CNASoundness
end

-- Lax253009.ManyTableConsistency
section
namespace Lax253009.ManyTableConsistency
end Lax253009.ManyTableConsistency
end

-- Lax253009.FAFTest
section
namespace Lax253009.FAFTest

open LongCode FiniteProbability CNASoundness

noncomputable def condition {Ω : Type} {u w q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (R : Table u) (ω : Ω) (g : Fin q → Coordinate u) : Coordinate w :=
  fun y ↦ valid ω y && decide (∀ j, g j (ρ ω y) = R (g j))

def Accepts {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (R : Table u) (A : Ω → Table w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u)
    (f : Fin n → Fin s → Coordinate w) : Prop :=
  ∀ i, AcceptsWithCondition (A (ω i)) (f i) (condition ρ valid R (ω i) g)

end Lax253009.FAFTest
end

-- Lax253009.LongCodePatterns
section
namespace Lax253009.LongCodePatterns

open LongCode

abbrev Pattern (w : ℕ) := Coordinate w → Option Bool

noncomputable def restrict {w : ℕ} (Q : Coordinate w → Prop) (A : Table w) :
    Pattern w := by
  classical
  exact fun g ↦ if Q g then some (A g) else none

def SideQueried {w s : ℕ} (f : Fin s → Coordinate w) (h g' : Coordinate w) : Prop :=
  ∃ g, Queried f g ∧ AgreesOn h g g'

noncomputable def sidePatterns {w s : ℕ} (f : Fin s → Coordinate w)
    (h : Coordinate w) : Finset (Pattern w) := by
  classical
  exact (Finset.univ.filter (fun A : Table w ↦ AcceptsWithCondition A f h)).image
    (restrict (SideQueried f h))

end Lax253009.LongCodePatterns
end

-- Lax253009.FAFPatterns
section
namespace Lax253009.FAFPatterns

open LongCode LongCodePatterns

noncomputable def conditionOfAnswers {Ω : Type} {u w q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Ω) (g : Fin q → Coordinate u) (b : Word q) : Coordinate w :=
  fun y ↦ valid ω y && decide (∀ j, g j (ρ ω y) = b j)

noncomputable def patterns {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    Finset (Word q × (Fin n → Pattern w)) := by
  classical
  exact Finset.univ.biUnion (fun b : Word q ↦
    (Fintype.piFinset (fun i ↦ sidePatterns (f i) (conditionOfAnswers ρ valid (ω i) g b))).image
      (fun a ↦ (b, a)))

noncomputable def transcript {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w) (R : Table u) (A : Ω → Table w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    Word q × (Fin n → Pattern w) :=
  (fun j ↦ R (g j), fun i ↦ restrict (SideQueried (f i) (FAFTest.condition ρ valid R (ω i) g)) (A (ω i)))

axiom transcript_mem {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w) (R : Table u) (A : Ω → Table w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w)
    (h : FAFTest.Accepts ρ valid R A ω g f) :
    transcript ρ valid R A ω g f ∈ patterns ρ valid ω g f

end Lax253009.FAFPatterns
end
