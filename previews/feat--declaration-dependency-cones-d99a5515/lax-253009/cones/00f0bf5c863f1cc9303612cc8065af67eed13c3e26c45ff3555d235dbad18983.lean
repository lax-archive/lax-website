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
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
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

axiom completeness {Z W A B : Type} (G : Game Z W A B)
    (P Q : W → A) (h : ∀ z, G.Wins P Q z) (t : ℕ) :
    ∀ z, (lift G t).Wins (fun w i ↦ P (w i)) (fun w i ↦ Q (w i)) z

end Lax253009.TupleFortification
end
