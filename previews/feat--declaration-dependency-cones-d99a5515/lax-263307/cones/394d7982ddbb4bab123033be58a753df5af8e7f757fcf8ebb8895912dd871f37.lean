-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic

-- Lax263307.LinearRelaxation
section
namespace Lax263307
end Lax263307

namespace Lax263307.LinearRelaxation
end Lax263307.LinearRelaxation

namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible
end

-- Lax263307.ConditionedCosts
section
namespace Lax263307.ConditionedCosts
end Lax263307.ConditionedCosts
end

-- Lax263307.ComponentCuts
section
namespace Lax263307.ComponentCuts
end Lax263307.ComponentCuts
end

-- Lax263307.SeparatorComponents
section
namespace Lax263307.SeparatorComponents.Partition
end Lax263307.SeparatorComponents.Partition

namespace Lax263307.SeparatorComponents

/-- The recursive answer is the union of the answers on the parts. -/
def combine {n : ℕ} {ι : Type} [Fintype ι] (I : ι → Finset (Fin n)) :
    Finset (Fin n) := Finset.univ.biUnion I

end Lax263307.SeparatorComponents
end

-- Lax263307.RecursiveRounding
section
namespace Lax263307.RecursiveRounding
end Lax263307.RecursiveRounding
end

-- Lax263307.ComponentCutEncoding
section
namespace Lax263307.ComponentCutEncoding
end Lax263307.ComponentCutEncoding
end

-- Lax263307.StrongComponentGaps
section
namespace Lax263307.StrongComponentGaps
end Lax263307.StrongComponentGaps
end

-- Lax263307.HeavyRecursiveRounding
section
namespace Lax263307.HeavyRecursiveRounding
end Lax263307.HeavyRecursiveRounding
end

-- Lax263307.ComputedRounding
section
namespace Lax263307.ComputedRounding.collect_correct
end Lax263307.ComputedRounding.collect_correct

namespace Lax263307.ComputedRounding

open SeparatorComponents (combine)

def target (δ cost : ℚ) : ℕ := ⌊(1 - δ) * cost⌋₊ + 1

def answer {n : ℕ} {ι : Type} (δ : ℚ) (k : ℕ) (cost : ι → ℚ)
    (query : ι → ℕ → Option (Finset (Fin n))) (i : ι) : Option (Finset (Fin n)) :=
  if δ * k / (4 * n) < cost i then query i (target δ (cost i)) else some ∅

inductive Result (n : ℕ)
  | found (vertices : Finset (Fin n))
  | cut (vertices : Finset (Fin n)) (bound : ℕ)

def collect {n : ℕ} {ι : Type} [Fintype ι] (order : List ι) (parts : ι → Finset (Fin n))
    (δ : ℚ) (k : ℕ) (cost : ι → ℚ) (query : ι → ℕ → Option (Finset (Fin n))) : Result n :=
  match order.find? (fun i => (answer δ k cost query i).isNone) with
  | some i => .cut (parts i) (target δ (cost i) - 1)
  | none => .found (combine (fun i => (answer δ k cost query i).getD ∅))

open LinearRelaxation SeparatorComponents

open ComponentCutEncoding

end Lax263307.ComputedRounding
end
