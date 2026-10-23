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

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.LongCode
section
namespace Lax323828.LongCode

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

end Lax323828.LongCode
end

-- Lax323828.CNASoundness
section
namespace Lax323828.CNASoundness
end Lax323828.CNASoundness
end

-- Lax323828.ManyTableConsistency
section
namespace Lax323828.ManyTableConsistency
end Lax323828.ManyTableConsistency
end

-- Lax323828.FAFTest
section
namespace Lax323828.FAFTest

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

end Lax323828.FAFTest
end

-- Lax323828.LongCodePatterns
section
namespace Lax323828.LongCodePatterns

open scoped Classical

open LongCode

/-- A partial Boolean answer table; `none` marks an unqueried coordinate. -/
abbrev Pattern (w : ℕ) := Coordinate w → Option Bool

/-- Record the table answers on the queried coordinates and leave the others unspecified. -/
noncomputable def restrict {w : ℕ} (Q : Coordinate w → Prop) (A : Table w) :
    Pattern w :=
  fun g ↦ if Q g then some (A g) else none

/-- A coordinate queried by the test or forced by agreement on the side condition. -/
def SideQueried {w s : ℕ} (f : Fin s → Coordinate w) (h g' : Coordinate w) : Prop :=
  ∃ g, Queried f g ∧ AgreesOn h g g'

/-- All queried answer patterns arising from tables accepted with the side condition. -/
noncomputable def sidePatterns {w s : ℕ} (f : Fin s → Coordinate w)
    (h : Coordinate w) : Finset (Pattern w) :=
  (Finset.univ.filter (fun A : Table w ↦ AcceptsWithCondition A f h)).image
    (restrict (SideQueried f h))

end Lax323828.LongCodePatterns
end

-- Lax323828.FAFPatterns
section
namespace Lax323828.FAFPatterns

open scoped Classical

open LongCode LongCodePatterns

/-- The side condition on a larger-table word: validity and agreement with all reference answers. -/
noncomputable def conditionOfAnswers {Ω : Type} {u w q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Ω) (g : Fin q → Coordinate u) (b : Word q) : Coordinate w :=
  fun y ↦ valid ω y && decide (∀ j, g j (ρ ω y) = b j)

/-- All reference answer strings paired with one permissible partial pattern for each sampled larger table. -/
noncomputable def patterns {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    Finset (Word q × (Fin n → Pattern w)) :=
  Finset.univ.biUnion (fun b : Word q ↦
    (Fintype.piFinset (fun i ↦ sidePatterns (f i) (conditionOfAnswers ρ valid (ω i) g b))).image
      (fun a ↦ (b, a)))

/-- The reference answers and queried larger-table answers supplied by the given tables. -/
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

end Lax323828.FAFPatterns
end
