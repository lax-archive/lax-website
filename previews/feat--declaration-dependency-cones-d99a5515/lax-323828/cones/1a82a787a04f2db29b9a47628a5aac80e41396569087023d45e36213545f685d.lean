-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828.FiniteProbability

open scoped Classical

open scoped BigOperators

/-- The proportion of points in the finite sample space satisfying the event `P`. -/
noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax323828.FiniteProbability
end

-- Lax323828.FortifiedSquaring
section
namespace Lax323828.FortifiedSquaring

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

def DoubleWins (P Q : W × W → A × A) (z : Z × Z) : Prop :=
  let a := P (G.left z.1, G.left z.2)
  let b := Q (G.right z.1, G.right z.2)
  G.Test z.1 a.1 b.1 ∧ G.Test z.2 a.2 b.2

end Game

axiom soundness {Z W A B : Type} [Fintype Z] [Nonempty Z] [Fintype B]
    (G : Game Z W A B) (s v η : ℝ) (hv : 0 ≤ v)
    (hs : G.Sound s) (hfort : G.Fortified v η)
    (P Q : W × W → A × A) :
    probability (G.DoubleWins P Q) ≤ v * s + (Fintype.card B : ℝ) * η

end Lax323828.FortifiedSquaring
end
