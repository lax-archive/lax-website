-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

-- Lax342547.PairedFrames
section
namespace Lax342547.PairedFrames

universe u v w z

variable {K : Type u} {U : Type v} {V : Type w} {W : Type z} [Field K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [hVdim : FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

axiom paired_matrix_orbit {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq N] (A A' : Matrix N I K) (B B' : Matrix N J K)
    (hA : Function.Injective A.mulVec) (hA' : Function.Injective A'.mulVec)
    (hB : Function.Injective B.mulVec) (hB' : Function.Injective B'.mulVec)
    (hgram : A.transpose * B = A'.transpose * B') :
    ∃ C D : Matrix N N K, C * D = 1 ∧ D * C = 1 ∧
      C * A = A' ∧ D.transpose * B = B'

end Lax342547.PairedFrames
end
