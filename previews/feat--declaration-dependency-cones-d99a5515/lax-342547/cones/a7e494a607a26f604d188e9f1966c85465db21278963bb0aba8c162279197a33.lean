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

def compatibility (Z : Matrix I E K) (W : Matrix I F K) :
    (Matrix E I K × Matrix I F K) →ₗ[K] Matrix E F K where
  toFun p := p.1 * W - Z.transpose * p.2
  map_add' x y := by simp [Matrix.add_mul, Matrix.mul_add, add_sub_add_comm]
  map_smul' c x := by simp [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

end Lax342547.MixerCompatibility
end
