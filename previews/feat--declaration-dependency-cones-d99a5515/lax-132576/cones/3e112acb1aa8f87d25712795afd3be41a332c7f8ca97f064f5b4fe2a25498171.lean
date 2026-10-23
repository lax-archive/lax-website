-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Computability.Halting
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite.Basic

-- Lax132576.LabelledAutomata
section
namespace Lax132576.LabelledAutomata.LabAut.Path
end Lax132576.LabelledAutomata.LabAut.Path

namespace Lax132576.LabelledAutomata

/-- An automaton whose finitely many transitions are labelled by an input string and
a label from `L`, with distinguished sets of initial and final states. -/
structure LabAut (A L Q : Type) where
  /-- The set of initial states. -/
  init : Set Q
  /-- The set of final states. -/
  final : Set Q
  /-- The transition relation. -/
  δ : Set (Q × List A × L × Q)
  /-- There are only finitely many transitions. -/
  δ_finite : δ.Finite

namespace LabAut

variable {A L Q : Type}

end LabAut

end Lax132576.LabelledAutomata
end

-- Lax132576.WeightedAutomata
section
namespace Lax132576.WeightedAutomata
end Lax132576.WeightedAutomata
end

-- Lax132576.WeightedCodes
section
namespace Lax132576.WeightedCodes

open Lax132576.LabelledAutomata Lax132576.WeightedAutomata

/-- A code of a weighted automaton over `ℚ`: transitions `(p, u, (a, b), q)` from
`p` to `q` reading `u` with weight `a / b`, and the initial and final states. -/
structure WCode where
  /-- The transitions `(p, u, (a, b), q)`. -/
  transitions : List (ℕ × List ℕ × (ℤ × ℕ) × ℕ)
  /-- The initial states. -/
  init : List ℕ
  /-- The final states. -/
  final : List ℕ

/-- The weighted automaton over `ℚ` described by a code. -/
def wcodeAut (c : WCode) : LabAut ℕ ℚ ℕ where
  init := {q | q ∈ c.init}
  final := {q | q ∈ c.final}
  δ := {t | ∃ s ∈ c.transitions, t = (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)}
  δ_finite := Set.Finite.ofFinset
    (c.transitions.toFinset.image
      (fun s => (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)))
    (by intro t; simp [eq_comm])

end Lax132576.WeightedCodes
end
