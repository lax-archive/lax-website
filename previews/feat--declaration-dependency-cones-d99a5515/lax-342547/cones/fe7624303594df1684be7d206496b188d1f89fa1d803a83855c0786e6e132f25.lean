-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

instance (b degree : ℕ) : Fintype (SelectorCoordinates b degree) :=
  inferInstanceAs (Fintype {S : Finset (Fin b) // S.card ≤ degree})

def selectorEval {b degree : ℕ} (s : Fin b → Binary)
    (c : SelectorCoordinates b degree) : Binary := ∏ i ∈ c.val, s i

variable {Label Coord Base : Type}

def baseEval (z : Base → Binary) : Option Base → Binary
  | none => 1
  | some i => z i

def point (p : Label → Coord → Binary) (s : Label) (z : Base → Binary)
    (i : Coord × Option Base) : Binary := p s i.1 * baseEval z i.2

def pointMoment (p : Label → Coord → Binary) (s : Label) (z : Base → Binary) :
    Matrix (Coord × Option Base) (Coord × Option Base) Binary :=
  fun i j => point p s z i * point p s z j

def momentSpace (p : Label → Coord → Binary) (A : Set Base) :
    Submodule Binary (Matrix (Coord × Option Base) (Coord × Option Base) Binary) :=
  Submodule.span Binary {w | ∃ s z, (∀ i, i ∉ A → z i = 0) ∧ w = pointMoment p s z}

end Lax342547.MomentSpace
end

-- Lax342547.BaseMoments
section
namespace Lax342547.BaseMoments

open Lax342547.MomentSpace

def IsBaseMoment {Base : Type} (Z : Matrix (Option Base) (Option Base) Binary) : Prop :=
  (∀ i j, Z i j = Z j i) ∧ ∀ i, Z i i = Z none i

end Lax342547.BaseMoments
end

-- Lax342547.LabelDecomposition
section
namespace Lax342547.LabelDecomposition

open Lax342547.MomentSpace Lax342547.BaseMoments

axiom low_rank_label_decomposition {Base : Type} [Fintype Base] {b degree R : ℕ}
    (w : Matrix (SelectorCoordinates b degree × Option Base)
      (SelectorCoordinates b degree × Option Base) Binary)
    (hw : w ∈ momentSpace (selectorEval (degree := degree)) Set.univ)
    (hrank : w.rank ≤ R) (hdegree : 6 * R + 4 ≤ degree) :
    ∃ L : Finset (Fin b → Binary),
    ∃ Z : (Fin b → Binary) → Matrix (Option Base) (Option Base) Binary,
      L.card ≤ R ∧ (∀ s ∈ L, IsBaseMoment (Z s)) ∧
      (∑ s ∈ L, (Z s).rank) ≤ R ∧
      ∀ i k, w i k = ∑ s ∈ L, selectorEval s i.1 * selectorEval s k.1 * Z s i.2 k.2

end Lax342547.LabelDecomposition
end
