-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Matrix.BilinearForm

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

def selectorEval {b degree : ℕ} (s : Fin b → Binary)
    (c : SelectorCoordinates b degree) : Binary := ∏ i ∈ c.val, s i

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.SparsePins
section
namespace Lax342547.SparsePins

open Lax342547.MomentSpace

variable {Label Coord Base : Type}

def labelTensor (p : Label → Coord → Binary) (s : Label) :
    (Base → Binary) →ₗ[Binary] (Coord × Base → Binary) where
  toFun z i := p s i.1 * z i.2
  map_add' z w := by ext i; exact mul_add _ _ _
  map_smul' a z := by ext i; exact mul_left_comm _ _ _

noncomputable def expansion (p : Label → Coord → Binary) :
    (Label →₀ (Base → Binary)) →ₗ[Binary] (Coord × Base → Binary) :=
  Finsupp.lsum Binary (labelTensor p)

axiom sparse_pin_labels {Base Component : Type} [Fintype Base] [Fintype Component]
    {b degree K R : ℕ}
    (U : Bool → Component → Submodule Binary (SelectorCoordinates b degree × Base → Binary))
    (hdim : ∀ sign e, Module.finrank Binary (U sign e) ≤ K)
    (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ B : Finset (Fin b → Binary),
      B.card ≤ 2 * Fintype.card Component * K * (R + 14) ∧
      ∀ sign e (c : (Fin b → Binary) →₀ (Base → Binary)),
        c.support.card ≤ R + 14 → expansion (selectorEval (degree := degree)) c ∈ U sign e →
        c.support ⊆ B

end Lax342547.SparsePins
end
