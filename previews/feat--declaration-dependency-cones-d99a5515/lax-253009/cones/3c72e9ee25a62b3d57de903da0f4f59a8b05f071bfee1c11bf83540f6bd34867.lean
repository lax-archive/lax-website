-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
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

def Fortified [Fintype Z] (v η : ℝ) : Prop :=
  ∀ (P Q : W → A) (S T : W → Prop),
    probability (fun z ↦ G.Wins P Q z ∧ S (G.left z) ∧ T (G.right z)) ≤
      v * probability (fun z ↦ S (G.left z) ∧ T (G.right z)) + η

end Game

end Lax253009.FortifiedSquaring
end
