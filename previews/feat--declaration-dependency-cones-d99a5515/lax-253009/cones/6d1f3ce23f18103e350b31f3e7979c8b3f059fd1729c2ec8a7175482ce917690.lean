-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax253009.BooleanFourier
section
namespace Lax253009.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def average {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) : ℝ :=
  (∑ x, F x) / (2 : ℝ) ^ Fintype.card ι

end Lax253009.BooleanFourier
end

-- Lax253009.FourierProjection
section
namespace Lax253009.FourierProjection

open BooleanFourier

def splice {ι : Type} [DecidableEq ι] (U : Finset ι) (x y : Cube ι) : Cube ι :=
  fun i ↦ if i ∈ U then x i else y i

noncomputable def project {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (U : Finset ι) (x : Cube ι) : ℝ :=
  average fun y ↦ F (splice U x y)

end Lax253009.FourierProjection
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

-- Lax253009.SideConditionAveraging
section
namespace Lax253009.SideConditionAveraging

open LongCode BooleanFourier FourierProjection

def satisfying {w : ℕ} (h : Coordinate w) : Finset (Word w) :=
  Finset.univ.filter fun x ↦ h x = true

axiom query_preserved {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) (hpass : AcceptsWithCondition A f h)
    (g : Coordinate w) (hg : Queried f g) :
  project (fun q ↦ sign (A q)) (satisfying h) g = sign (A g)

end Lax253009.SideConditionAveraging
end
