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

axiom paired_frame_orbit {K : Type u} {U : Type v} {V : Type w} {W : Type z} [Field K]
    [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A A' : U →ₗ[K] V) (B B' : W →ₗ[K] Module.Dual K V)
    (hA : Function.Injective A) (hA' : Function.Injective A')
    (hB : Function.Injective B) (hB' : Function.Injective B')
    (hgram : ∀ u w, B w (A u) = B' w (A' u)) :
    ∃ L : V ≃ₗ[K] V, (∀ u, L (A u) = A' u) ∧
      ∀ w v, B w (L.symm v) = B' w v

end Lax342547.PairedFrames
end
