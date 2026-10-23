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
end Lax342547.Walsh
end

-- Lax342547.FourierTests
section
namespace Lax342547.FourierTests
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

def crossBits {I J S : Type} [Fintype I] [Fintype J] (C : S → Matrix I J Binary) (N : ℕ)
    (xy : ((Fin N × I → Binary) × (Fin N × J → Binary))) : S → Binary :=
  fun s => dotProduct xy.1 ((bitMatrix (C s) N).mulVec xy.2)

end Lax342547.CrossBatchMixing
end

-- Lax342547.CrossGramBasis
section
namespace Lax342547.CrossGramBasis

open Lax342547.MomentSpace Lax342547.CrossBatchMixing

open scoped BigOperators

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

abbrev Slots (I J K L : Type) := (I × L) ⊕ (J × K)

def tests {I J K L : Type} [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] :
    Slots I J K L → Matrix (I ⊕ J) (K ⊕ L) Binary
  | Sum.inl (i,l) => fun a b => if a = Sum.inl i ∧ b = Sum.inr l then 1 else 0
  | Sum.inr (j,k) => fun a b => if a = Sum.inr j ∧ b = Sum.inl k then 1 else 0

axiom mutual_gram_bits (N : ℕ)
    (xy : (Fin N × (I ⊕ J) → Binary) × (Fin N × (K ⊕ L) → Binary)) :
    (∀ i l,crossBits tests N xy (Sum.inl (i,l)) = ∑ a,xy.1 (a,Sum.inl i)*xy.2 (a,Sum.inr l)) ∧
    (∀ j k,crossBits tests N xy (Sum.inr (j,k)) = ∑ a,xy.1 (a,Sum.inr j)*xy.2 (a,Sum.inl k))

end Lax342547.CrossGramBasis
end
