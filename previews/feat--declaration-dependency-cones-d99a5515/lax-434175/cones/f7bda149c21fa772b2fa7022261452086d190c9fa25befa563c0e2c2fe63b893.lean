-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Field.Rat

-- Lax434175.Problems
section
namespace Lax434175.Problems.DecisionReduction
end Lax434175.Problems.DecisionReduction

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

/-- The data of an embedding of `A` into `B`: a map on instances and
translations of solutions in both directions. -/
structure Embedding (A B : Problem) where
  map : A.Inst → B.Inst
  forth : (x : A.Inst) → A.Sched x → B.Sched (map x)
  back : (x : A.Inst) → B.Sched (map x) → A.Sched x

/-- The restriction of a problem to the instances satisfying `φ`. -/
def Problem.restrict (P : Problem) (φ : P.Inst → Prop) : Problem where
  Inst := { x : P.Inst // φ x }
  Sched x := P.Sched x.1
  feasible x σ := P.feasible x.1 σ
  cost x σ := P.cost x.1 σ

/-- The inclusion of a restricted problem into the unrestricted one. -/
def Problem.inclusion (P : Problem) (φ : P.Inst → Prop) : Embedding (P.restrict φ) P where
  map x := x.1
  forth _ σ := σ
  back _ σ := σ

end Lax434175.Problems
end
