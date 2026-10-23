-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Field.Rat

-- Lax434175.Problems
section
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

/-- Some feasible solution of the instance has cost at most the threshold. -/
def Problem.Decides (P : Problem) (x : P.Inst) (D : ℚ) : Prop :=
  ∃ σ, P.feasible x σ ∧ P.cost x σ ≤ D

/-- The data of a reduction between decision versions: an instance and a
threshold of `A` are mapped to an instance and a threshold of `B`. -/
structure DecisionReduction (A B : Problem) where
  map : A.Inst → ℤ → B.Inst
  threshold : A.Inst → ℤ → ℤ

/-- A reduction is sound if it preserves the answer. -/
def DecisionReduction.Sound {A B : Problem} (r : DecisionReduction A B) : Prop :=
  ∀ x (D : ℤ), A.Decides x D ↔ B.Decides (r.map x D) (r.threshold x D)

/-- The decision version of `A` reduces to that of `B`. -/
def Reducible (A B : Problem) : Prop := ∃ r : DecisionReduction A B, r.Sound

end Lax434175.Problems
end
