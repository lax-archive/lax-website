-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
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

def Fortified [Fintype Z] (v η : ℝ) : Prop :=
  ∀ (P Q : W → A) (S T : W → Prop),
    probability (fun z ↦ G.Wins P Q z ∧ S (G.left z) ∧ T (G.right z)) ≤
      v * probability (fun z ↦ S (G.left z) ∧ T (G.right z)) + η

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

def lift {Z W A B : Type} (G : Game Z W A B) (t : ℕ) :
    Game (Z × (History t W × History t W)) (Fin t → W) (Fin t → A) B where
  left z := plant (G.left z.1) z.2.1
  right z := plant (G.right z.1) z.2.2
  validLeft z a := G.validLeft z.1 (a z.2.1.1)
  validRight z b := G.validRight z.1 (b z.2.2.1)
  projectLeft z a := G.projectLeft z.1 (a z.2.1.1)
  projectRight z b := G.projectRight z.1 (b z.2.2.1)

axiom fortification {Z W A B : Type}
    [Fintype Z] [Nonempty Z] [Fintype W] [DecidableEq W] [Nonempty W]
    [Fintype A] [Nonempty A]
    (G : Game Z W A B)
    (hl : ∀ f : W → ℝ, (𝔼 z, f (G.left z)) = (𝔼 w, f w))
    (hr : ∀ f : W → ℝ, (𝔼 z, f (G.right z)) = (𝔼 w, f w))
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hG : G.Sound s)
    (t : ℕ) (ht : 0 < t) (r : ℝ) (hr0 : 0 ≤ r) (htr : 1 / (t : ℝ) ≤ r ^ 2) :
    (lift G t).Fortified s (4 * r)

end Lax253009.TupleFortification
end
