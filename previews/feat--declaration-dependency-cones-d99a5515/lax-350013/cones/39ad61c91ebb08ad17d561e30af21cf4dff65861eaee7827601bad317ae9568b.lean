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

-- Lax350013.ExactTriangle
section
namespace Lax350013.ExactTriangle
end Lax350013.ExactTriangle

namespace Lax350013.ExactTriangle.ExactTriangle
end Lax350013.ExactTriangle.ExactTriangle
end

-- Lax350013.ZeroWeightClique
section
namespace Lax350013.ZeroWeightClique
end Lax350013.ZeroWeightClique
end

-- Lax350013.CliqueOptimization
section
namespace Lax350013.CliqueOptimization

open Finset

/-- The total edge weight of the `k`-clique that has the vertex `v p` in part `p` (Corollary 39):
the sum, over the pairs of parts `p < q`, of the weight between `v p` and `v q`. -/
def cliqueWeight {k n : ℕ} (w : Fin k → Fin k → Fin n → Fin n → ℤ) (v : Fin k → Fin n) : ℤ :=
  ∑ p : Fin k, ∑ q ∈ Finset.univ.filter (fun q : Fin k => p < q), w p q (v p) (v q)

end Lax350013.CliqueOptimization
end
