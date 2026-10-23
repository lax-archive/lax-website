-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

-- Lax916827.StreamingStringTransducers
section
namespace Lax916827.StreamingStringTransducers.SST.subst
end Lax916827.StreamingStringTransducers.SST.subst

namespace Lax916827.StreamingStringTransducers

/-- A register update is copyless if each register name occurs at most once in the
concatenation of the strings assigned to the registers. -/
def Copyless {X B : Type} [Fintype X] (u : X → List (X ⊕ B)) : Prop :=
  ((Finset.univ.toList.map u).flatten.filterMap
      (fun z => match z with | Sum.inl x => some x | Sum.inr _ => none)).Nodup

/-- A streaming string transducer with states `Q` and registers `X`. -/
structure SST (A B Q X : Type) [Fintype X] where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a new state and a register update. -/
  step : Q → A → Q × (X → List (X ⊕ B))
  /-- Every register update is copyless. -/
  step_copyless : ∀ q a, Copyless (step q a).2
  /-- The final output string, chosen by the final state. -/
  final : Q → List (X ⊕ B)

namespace SST

variable {A B Q X : Type} [Fintype X]

end SST

end Lax916827.StreamingStringTransducers
end
