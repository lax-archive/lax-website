-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

-- Lax350013.WordRAM
section
namespace Lax350013
end Lax350013

namespace Lax350013.WordRAM
end Lax350013.WordRAM

namespace Lax350013.WordRAM.Instr
end Lax350013.WordRAM.Instr

namespace Lax350013.WordRAM.exec
end Lax350013.WordRAM.exec

namespace Lax350013.WordRAM.Instr.accept
end Lax350013.WordRAM.Instr.accept

namespace Lax350013.WordRAM.Instr.add
end Lax350013.WordRAM.Instr.add

namespace Lax350013.WordRAM.Instr.bltz
end Lax350013.WordRAM.Instr.bltz

namespace Lax350013.WordRAM.Instr.load
end Lax350013.WordRAM.Instr.load

namespace Lax350013.WordRAM.Instr.mul
end Lax350013.WordRAM.Instr.mul

namespace Lax350013.WordRAM.Instr.one
end Lax350013.WordRAM.Instr.one

namespace Lax350013.WordRAM.Instr.reject
end Lax350013.WordRAM.Instr.reject

namespace Lax350013.WordRAM.Instr.store
end Lax350013.WordRAM.Instr.store

namespace Lax350013.WordRAM.Instr.sub
end Lax350013.WordRAM.Instr.sub
end

-- Lax350013.PolynomialTime
section
namespace Lax350013.PolynomialTime
end Lax350013.PolynomialTime

namespace Lax350013.PolynomialTime.Problem
end Lax350013.PolynomialTime.Problem
end

-- Lax350013.RAMResources
section
namespace Lax350013.RAMResources
end Lax350013.RAMResources

namespace Lax350013.RAMResources.Problem
end Lax350013.RAMResources.Problem

namespace Lax350013.RAMResources.RunsPhases
end Lax350013.RAMResources.RunsPhases

namespace Lax350013.RAMResources.Serves
end Lax350013.RAMResources.Serves
end

-- Lax350013.ThinMatrices
section
namespace Lax350013.ThinMatrices
end Lax350013.ThinMatrices

namespace Lax350013.ThinMatrices.ThinInstance
end Lax350013.ThinMatrices.ThinInstance

namespace Lax350013.ThinMatrices.ThinPair
end Lax350013.ThinMatrices.ThinPair
end

-- Lax350013.HintedMatrixVector
section
namespace Lax350013.HintedMatrixVector

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

open Lax350013.ThinMatrices

namespace HintedMv

/-- Section 5.4, uMv-hinted uMv (Conjecture 5.12 of [vdBNS19]): "n^{ω(1,τ₁,1)-ε} for Phase 2,
n^{ω(τ₂,τ₁,1)-ε} for Phase 3, and n^{τ₁+τ₂-ε} for Phase 4."  `Achieves a₂ a₃ a₄` stands for "some
algorithm solves the problem with t₁ = n^{τ₁} and t₂ = n^{τ₂}, with polynomial time in Phase 1 and
O(n^{a₂}), O(n^{a₃}), O(n^{a₄}) time in Phases 2, 3, 4"; `ω₂` stands for ω(1,τ₁,1) and `ω₃` for
ω(τ₂,τ₁,1).  For programs of the word RAM the parameter is `AchievesUMvHinted τ₁ τ₂`. -/
def Conjecture512 (Achieves : ℝ → ℝ → ℝ → Prop) (ω₂ ω₃ τ₁ τ₂ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω₂ - ε) (ω₃ - ε) (τ₁ + τ₂ - ε)

end HintedMv

open HintedMv

end Lax350013.HintedMatrixVector
end
