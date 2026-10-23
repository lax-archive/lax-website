-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sublists
import Mathlib.Data.Rat.Cast.Order
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

-- Lax263307.ConditioningDistribution
section
namespace Lax263307.ConditioningDistribution
end Lax263307.ConditioningDistribution
end

-- Lax263307.Entropy
section
namespace Lax263307
end Lax263307

namespace Lax263307.Entropy
end Lax263307.Entropy
end

-- Lax263307.EntropyBounds
section
namespace Lax263307.EntropyBounds
end Lax263307.EntropyBounds
end

-- Lax263307.EntropyGap
section
namespace Lax263307.EntropyGap
end Lax263307.EntropyGap
end

-- Lax263307.RationalConditioning
section
namespace Lax263307.RationalConditioning

open LinearRelaxation Entropy

/-- Enumerate only sublists with lengths between zero and the conditioning budget. -/
def candidates (n r : ℕ) : List (Finset (Fin n)) :=
  (List.range (r + 1)).flatMap fun j =>
    ((List.finRange n).sublistsLen j).map List.toFinset

end Lax263307.RationalConditioning
end

-- Lax263307.CoordinateCatalog
section
namespace Lax263307.CoordinateCatalog

open LinearRelaxation RationalConditioning

private theorem mem_candidates (n r : ℕ) (A : Finset (Fin n)) :
    A ∈ candidates n r ↔ A.card ≤ r :=
  ⟨fun member =>
    let ⟨j, inRange, inSublists⟩ := List.mem_flatMap.mp member
    let ⟨vertices, listed, sameSet⟩ := List.mem_map.mp inSublists
    let sublist := (List.mem_sublistsLen.mp listed).1
    let length := (List.mem_sublistsLen.mp listed).2
    calc
      A.card = vertices.toFinset.card := congrArg Finset.card sameSet.symm
      _ = vertices.length := List.toFinset_card_of_nodup (sublist.nodup (List.nodup_finRange n))
      _ = j := length
      _ ≤ r := Nat.le_of_lt_succ (List.mem_range.mp inRange),
   fun bounded =>
    let vertices := (List.finRange n).filter fun v => decide (v ∈ A)
    let sublist : vertices.Sublist (List.finRange n) := List.filter_sublist
    let sameSet : vertices.toFinset = A := Finset.ext fun v =>
      List.mem_toFinset.trans (List.mem_filter.trans
        ⟨fun h => of_decide_eq_true h.2,
         fun h => ⟨List.mem_finRange v, decide_eq_true h⟩⟩)
    let length : vertices.length = A.card :=
      (List.toFinset_card_of_nodup (sublist.nodup (List.nodup_finRange n))).symm.trans
        (congrArg Finset.card sameSet)
    List.mem_flatMap.mpr ⟨A.card, List.mem_range.mpr (Nat.lt_succ_of_le bounded),
      List.mem_map.mpr ⟨vertices, List.mem_sublistsLen.mpr ⟨sublist, length⟩, sameSet⟩⟩⟩

end Lax263307.CoordinateCatalog
end
