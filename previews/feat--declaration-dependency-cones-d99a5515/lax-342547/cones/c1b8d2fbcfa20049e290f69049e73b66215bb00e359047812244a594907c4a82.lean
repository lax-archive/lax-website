-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
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

-- Lax342547.CutSparsity
section
namespace Lax342547.CutSparsity

open Lax342547.MomentSpace Lax342547.CutProfiles

variable {Tag V : Type} [AddCommGroup V] [Module Binary V]

noncomputable def valueCount (w : Tag → V) (c : V) : ℕ := Nat.card {t : Tag // w t = c}

axiom majority_unique [Fintype Tag] [Nonempty Tag] (w v : Tag → V)
    (hcut : cutMap w = cutMap v)
    (hw : Fintype.card Tag < 2 * valueCount w 0)
    (hv : Fintype.card Tag < 2 * valueCount v 0) : w = v

end Lax342547.CutSparsity
end
