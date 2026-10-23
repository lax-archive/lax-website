-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

-- Lax263307.GraphClasses
section
namespace Lax263307
end Lax263307

namespace Lax263307.GraphClasses
end Lax263307.GraphClasses
end

-- Lax263307.EdgeSublinearSeparators
section
namespace Lax263307.EdgeSublinearSeparators
end Lax263307.EdgeSublinearSeparators
end

-- Lax263307.LinearRelaxation
section
namespace Lax263307
end Lax263307

namespace Lax263307.LinearRelaxation
end Lax263307.LinearRelaxation

namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible
end

-- Lax263307.SeparatorComponents
section
namespace Lax263307.SeparatorComponents
end Lax263307.SeparatorComponents

namespace Lax263307.SeparatorComponents.Partition
end Lax263307.SeparatorComponents.Partition
end

-- Lax263307.BalancedPartitions
section
namespace Lax263307.BalancedPartitions
end Lax263307.BalancedPartitions
end

-- Lax263307.Entropy
section
namespace Lax263307
end Lax263307

namespace Lax263307.Entropy
end Lax263307.Entropy
end

-- Lax263307.PathSampling
section
namespace Lax263307.PathSampling
end Lax263307.PathSampling

namespace Lax263307.PathSampling.Distribution
end Lax263307.PathSampling.Distribution
end

-- Lax263307.RepeatedCutAccounting
section
namespace Lax263307.RepeatedCutAccounting

noncomputable def cost {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ v ∈ S, x v

end Lax263307.RepeatedCutAccounting
end

-- Lax263307.CutTraces
section
namespace Lax263307.CutTraces.parts
end Lax263307.CutTraces.parts

namespace Lax263307.CutTraces

open RepeatedCutAccounting (cost)

open SeparatorComponents EdgeSublinearSeparators

structure Trace {n : ℕ} (G : SimpleGraph (Fin n)) (start : Finset (Fin n)) (steps : ℕ) where
  remaining : ℕ → Finset (Fin n)
  left : ℕ → Finset (Fin n)
  right : ℕ → Finset (Fin n)
  initial : remaining 0 = start
  cover : ∀ i < steps, left i ∪ right i = remaining i
  next : ∀ i < steps, remaining (i + 1) = left i \ right i
  nonempty : ∀ i < steps, (right i).Nonempty
  small_piece : ∀ i < steps, 2 * (right i \ left i).card ≤ (remaining i).card
  separated : ∀ i < steps, ∀ u ∈ left i \ right i, ∀ v ∈ right i \ left i, ¬G.Adj u v

noncomputable def separator {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) : Finset (Fin n) := Finset.univ.biUnion fun i : Fin q => T.left i ∩ T.right i

end Lax263307.CutTraces
end
