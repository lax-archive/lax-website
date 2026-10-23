-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
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

end Game

end Lax323828.FortifiedSquaring
end

-- Lax323828.TupleFortification
section
namespace Lax323828.TupleFortification

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

axiom soundness {Z W A B : Type} [Fintype Z] [Fintype W] [DecidableEq W]
    [Nonempty W] [Fintype A] (G : Game Z W A B) (t : ℕ) (ht : 0 < t)
    (s : ℝ) (hG : G.Sound s) : (lift G t).Sound s

end Lax323828.TupleFortification
end
