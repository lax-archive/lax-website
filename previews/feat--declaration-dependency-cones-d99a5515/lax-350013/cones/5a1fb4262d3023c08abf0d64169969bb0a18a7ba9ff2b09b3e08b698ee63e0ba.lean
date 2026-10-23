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

/-- Section 5.4: "Each conjecture asserts that no algorithm simultaneously beats all of its listed
bounds, for any ε > 0." v-hinted Mv (Conjecture 5.2 of [vdBNS19]): "Bounds conjectured to be
impossible to achieve simultaneously: n^{ω(1,1,τ)-ε} for Phase 2 and n^{1+τ-ε} for Phase 3."

Running times are not defined here, so the conjecture is stated relative to a parameter:
`Achieves a₂ a₃` stands for "some algorithm solves the problem with t = n^τ, with polynomial time in
Phase 1, O(n^{a₂}) time in Phase 2 and O(n^{a₃}) time in Phase 3".  `ω` stands for the number
ω(1,1,τ).  For programs of the word RAM the parameter is `AchievesVHinted τ`.  The exponents of
rectangular matrix multiplication are not defined in Lean: `ω` is an arbitrary real number here, and
the definition says something only together with a condition on it. The statement that the
conjecture fails (`Items.Corollary_40_fail`) is made for every `ω ≥ 2`.

[vdBNS19] words the bounds as lower bounds Ω(n^{x-ε}) on the time of a phase.  That wording implies
the one used here, "not O(n^{x-ε})" (apply it with ε/2), so a refutation of the conjecture in this
form refutes it as worded there.  The same holds for `Conjecture57` and `Conjecture512`. -/
def Conjecture52 (Achieves : ℝ → ℝ → Prop) (ω τ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω - ε) (1 + τ - ε)

end HintedMv

open HintedMv

end Lax350013.HintedMatrixVector
end
