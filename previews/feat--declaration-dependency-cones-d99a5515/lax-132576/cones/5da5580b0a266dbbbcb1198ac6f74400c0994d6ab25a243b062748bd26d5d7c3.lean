-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Computability.Halting
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite.Basic

-- Lax132576.LabelledAutomata
section
namespace Lax132576
end Lax132576

namespace Lax132576.LabelledAutomata
end Lax132576.LabelledAutomata

namespace Lax132576.LabelledAutomata.LabAut
end Lax132576.LabelledAutomata.LabAut

namespace Lax132576.LabelledAutomata.LabAut.Path
end Lax132576.LabelledAutomata.LabAut.Path
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

/-- A code is the tuple of its three lists. -/
def wcodeEquiv : WCode ≃ List (ℕ × List ℕ × (ℤ × ℕ) × ℕ) × List ℕ × List ℕ where
  toFun c := (c.transitions, c.init, c.final)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv := by rintro ⟨t, i, f⟩; rfl
  right_inv := by rintro ⟨t, i, f⟩; rfl

end Lax132576.WeightedCodes
end
