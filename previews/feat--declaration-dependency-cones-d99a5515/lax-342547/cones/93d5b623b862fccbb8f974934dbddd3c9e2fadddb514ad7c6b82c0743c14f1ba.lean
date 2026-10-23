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

axiom compatible_extensions (Z : Matrix I E K) (W : Matrix I F K)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec)
    (A : Matrix E I K) (B : Matrix I F K) :
    (∃ L : Matrix I I K, Z.transpose * L = A ∧ L * W = B) ↔ A * W = Z.transpose * B

end Lax342547.MixerCompatibility
end
