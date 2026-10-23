-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

-- Lax342547.MixerCompatibility
section
namespace Lax342547.MixerCompatibility

variable {K I E F : Type} [Field K] [Fintype I] [Fintype E] [Fintype F]

def restrictions (Z : Matrix I E K) (W : Matrix I F K) :
    Matrix I I K →ₗ[K] Matrix E I K × Matrix I F K where
  toFun L := (Z.transpose * L, L * W)
  map_add' L M := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c L := by simp [Matrix.mul_smul, Matrix.smul_mul]

axiom restrictions_codimension (Z : Matrix I E K) (W : Matrix I F K)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec) :
    Module.finrank K (LinearMap.range (restrictions Z W)) + Fintype.card E * Fintype.card F =
      Fintype.card E * Fintype.card I + Fintype.card I * Fintype.card F

end Lax342547.MixerCompatibility
end
