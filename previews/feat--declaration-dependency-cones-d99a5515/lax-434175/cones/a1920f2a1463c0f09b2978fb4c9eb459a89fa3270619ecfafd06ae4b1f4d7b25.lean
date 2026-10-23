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

/-- The composition of two embeddings. -/
def Embedding.comp {A B C : Problem} (e : Embedding A B) (f : Embedding B C) : Embedding A C where
  map x := f.map (e.map x)
  forth x σ := f.forth (e.map x) (e.forth x σ)
  back x τ := e.back x (f.back (e.map x) τ)

end Lax434175.Problems
end
