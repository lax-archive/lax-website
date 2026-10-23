-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.NNRat.Defs

-- Lax434175.Kernels
section
namespace Lax434175
end Lax434175

namespace Lax434175.Kernels
end Lax434175.Kernels

namespace Lax434175.Kernels.Kernel
end Lax434175.Kernels.Kernel
end

-- Lax434175.Modules
section
namespace Lax434175.Modules
end Lax434175.Modules

namespace Lax434175.Modules.Module
end Lax434175.Modules.Module

namespace Lax434175.Modules.Objective
end Lax434175.Modules.Objective

namespace Lax434175.Modules.Module.Sound
end Lax434175.Modules.Module.Sound

namespace Lax434175.Modules.Objective.Sound
end Lax434175.Modules.Objective.Sound
end

-- Lax434175.Problems
section
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

/-- An embedding is sound if both translations preserve feasibility and do
not increase the cost. -/
structure Embedding.Sound {A B : Problem} (e : Embedding A B) : Prop where
  forth_feasible : ∀ x σ, A.feasible x σ → B.feasible (e.map x) (e.forth x σ)
  forth_cost : ∀ x σ, A.feasible x σ → B.cost (e.map x) (e.forth x σ) ≤ A.cost x σ
  back_feasible : ∀ x τ, B.feasible (e.map x) τ → A.feasible x (e.back x τ)
  back_cost : ∀ x τ, B.feasible (e.map x) τ → A.cost x (e.back x τ) ≤ B.cost (e.map x) τ

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

end Lax434175.Problems
end

-- Lax434175.Assembly
section
namespace Lax434175.Assembly
end Lax434175.Assembly

namespace Lax434175.Assembly.Family
end Lax434175.Assembly.Family

namespace Lax434175.Assembly.Inst
end Lax434175.Assembly.Inst

namespace Lax434175.Assembly.Spec
end Lax434175.Assembly.Spec

namespace Lax434175.Assembly.Family.Sound
end Lax434175.Assembly.Family.Sound
end

-- Lax434175.Parameters
section
namespace Lax434175.Parameters.FieldParameter
end Lax434175.Parameters.FieldParameter

namespace Lax434175.Parameters.InPlace
end Lax434175.Parameters.InPlace

namespace Lax434175.Parameters

open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly

/-- `A` reduces to `B` by a reduction that relates the parameter values of
an instance and of its image by `R`. -/
def ReducibleWith {A B : Problem} {α β : Type} (κA : A.Inst → α) (κB : B.Inst → β)
    (R : α → β → Prop) : Prop :=
  ∃ r : DecisionReduction A B, r.Sound ∧ ∀ x D, R (κA x) (κB (r.map x D))

axiom reducibleWith_of_embedding {A B : Problem} {α β : Type} (e : Embedding A B)
    (κA : A.Inst → α) (κB : B.Inst → β) (R : α → β → Prop) :
    e.Sound → (∀ x, R (κA x) (κB (e.map x))) → ReducibleWith κA κB R

end Lax434175.Parameters
end
