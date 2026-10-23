-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Pi

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.CutProfiles
section
namespace Lax342547.CutProfiles

open Lax342547.MomentSpace

def Component (Tag : Type) := {e : Finset Tag // e.card = 2}

variable {Tag V : Type} [AddCommGroup V] [Module Binary V]

def cutMap : (Tag → V) →ₗ[Binary] (Component Tag → V) where
  toFun w e := ∑ t ∈ e.val, w t
  map_add' w v := by ext e; simp [Finset.sum_add_distrib]
  map_smul' c w := by ext e; simp [Finset.smul_sum]

end Lax342547.CutProfiles
end

-- Lax342547.CutFunctionals
section
namespace Lax342547.CutFunctionals

open Lax342547.MomentSpace Lax342547.CutProfiles

axiom representative_sums_eq {Tag V : Type} [Fintype Tag] [DecidableEq Tag]
    [Nonempty Tag] [AddCommGroup V] [Module Binary V]
    (W : Tag → Submodule Binary V) (ηO ηS : V →ₗ[Binary] Binary)
    (hO : ∀ c ∈ ⨅ t, W t, ηO c = 0) (hodd : Odd (Fintype.card Tag))
    (w v : Tag → V) (hw : ∀ t, w t ∈ W t) (hv : ∀ t, v t ∈ W t)
    (heq : cutMap w = cutMap v) :
    (∑ t, ηO (w t)) = (∑ t, ηO (v t)) ∧
      ∀ t, (∑ l ∈ Finset.univ.erase t, ηS (w l)) =
        ∑ l ∈ Finset.univ.erase t, ηS (v l)

end Lax342547.CutFunctionals
end
