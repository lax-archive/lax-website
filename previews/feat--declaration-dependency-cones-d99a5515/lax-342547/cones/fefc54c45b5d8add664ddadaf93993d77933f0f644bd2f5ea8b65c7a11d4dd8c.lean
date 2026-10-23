-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Real.Lemmas

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh

open Lax342547.MomentSpace

noncomputable def sign (z : Binary) : ℝ := if z = 0 then 1 else -1

noncomputable def phase {I : Type} [Fintype I] (x y : I → Binary) : ℝ :=
  sign (dotProduct x y)

end Lax342547.Walsh
end

-- Lax342547.FourierTests
section
namespace Lax342547.FourierTests

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def characterMean {Ω I : Type} [Fintype Ω] [Fintype I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target t : I → Binary) : ℝ :=
  ∑ ω, ρ ω * phase t (bits ω) * phase t target

end Lax342547.FourierTests
end

-- Lax342547.PushforwardWalsh
section
namespace Lax342547.PushforwardWalsh
end Lax342547.PushforwardWalsh
end

-- Lax342547.RetainedImages
section
namespace Lax342547.RetainedImages
end Lax342547.RetainedImages
end

-- Lax342547.RelativeEntropy
section
namespace Lax342547.RelativeEntropy
end Lax342547.RelativeEntropy
end

-- Lax342547.ConditionedMixing
section
namespace Lax342547.ConditionedMixing
end Lax342547.ConditionedMixing
end

-- Lax342547.BilinearWalsh
section
namespace Lax342547.BilinearWalsh
end Lax342547.BilinearWalsh
end

-- Lax342547.SlotWalsh
section
namespace Lax342547.SlotWalsh

open Lax342547.MomentSpace

def bitMatrix {I J : Type} (C : Matrix I J Binary) (N : ℕ) :
    Matrix (Fin N × I) (Fin N × J) Binary :=
  fun x y => if x.1 = y.1 then C x.2 y.2 else 0

end Lax342547.SlotWalsh
end

-- Lax342547.CrossBatchMixing
section
namespace Lax342547.CrossBatchMixing

open Lax342547.MomentSpace Lax342547.SlotWalsh Lax342547.FourierTests Lax342547.RelativeEntropy

noncomputable def coefficient {I J S : Type} [Fintype S]
    (C : S → Matrix I J Binary) (t : S → Binary) : Matrix I J Binary := ∑ s,t s • C s

def crossBits {I J S : Type} [Fintype I] [Fintype J] (C : S → Matrix I J Binary) (N : ℕ)
    (xy : ((Fin N × I → Binary) × (Fin N × J → Binary))) : S → Binary :=
  fun s => dotProduct xy.1 ((bitMatrix (C s) N).mulVec xy.2)

axiom weighted_character_bound {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    [DecidableEq I] [DecidableEq J] (C : S → Matrix I J Binary) (N : ℕ)
    (α f : (Fin N × I → Binary) → ℝ) (β g : (Fin N × J → Binary) → ℝ)
    (target t : S → Binary) (C₁ C₂ : ℝ)
    (hα : ∀ x,0 ≤ α x ∧ α x ≤ C₁/(2 : ℝ)^(N*Fintype.card I))
    (hβ : ∀ y,0 ≤ β y ∧ β y ≤ C₂/(2 : ℝ)^(N*Fintype.card J))
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hC : coefficient C t ≠ 0) :
    |characterMean (fun xy : (Fin N × I → Binary) × (Fin N × J → Binary) =>
      α xy.1*β xy.2*(f xy.1*g xy.2)) (crossBits C N) target t| ≤
      C₁*C₂/Real.sqrt ((2 : ℝ)^N)

end Lax342547.CrossBatchMixing
end
