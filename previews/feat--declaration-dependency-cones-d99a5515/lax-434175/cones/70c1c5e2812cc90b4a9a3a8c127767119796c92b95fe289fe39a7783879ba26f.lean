-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators

-- Lax434175.Problems
section
namespace Lax434175.Problems.DecisionReduction
end Lax434175.Problems.DecisionReduction

namespace Lax434175.Problems.Embedding
end Lax434175.Problems.Embedding

namespace Lax434175.Problems.Embedding.Sound
end Lax434175.Problems.Embedding.Sound

namespace Lax434175.Problems

/-- A minimization problem. -/
structure Problem where
  /-- The instances. -/
  Inst : Type
  /-- The candidate solutions of an instance. -/
  Sched : Inst → Type
  /-- Which candidate solutions are feasible. -/
  feasible : (x : Inst) → Sched x → Prop
  /-- The cost of a candidate solution. -/
  cost : (x : Inst) → Sched x → ℚ

end Lax434175.Problems
end

-- Lax434175.MachineCovering
section
namespace Lax434175.MachineCovering

open Lax434175.Problems

structure Inst where
  jobs : ℕ
  machines : ℕ
  p : Fin jobs → ℕ

/-- The load of a machine. -/
def load (x : Inst) (σ : Fin x.jobs → Fin x.machines) (i : Fin x.machines) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = i), x.p j

/-- The smallest load of a machine; `0` without machines. -/
def minLoad (x : Inst) (σ : Fin x.jobs → Fin x.machines) : ℕ :=
  if h : 0 < x.machines then Finset.univ.inf' ⟨⟨0, h⟩, Finset.mem_univ _⟩ (load x σ) else 0

/-- `P || C_min` -/
def problem : Problem where
  Inst := Inst
  Sched x := Fin x.jobs → Fin x.machines
  feasible _ _ := True
  cost x σ := -(minLoad x σ : ℚ)

end Lax434175.MachineCovering
end
