-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Halting
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

-- Lax132576.RationalRelations
section
namespace Lax132576.RationalRelations
end Lax132576.RationalRelations

namespace Lax132576.RationalRelations.NFAO
end Lax132576.RationalRelations.NFAO
end

-- Lax132576.TransducerCodes
section
namespace Lax132576.TransducerCodes

open Lax132576.LabelledAutomata Lax132576.RationalRelations

/-- A code of an automaton with output over the alphabet `ℕ` with states in `ℕ`:
its transitions `(p, u, v, q)` and its initial and final states. -/
structure RelCode where
  /-- The transitions `(p, u, v, q)`: from `p` to `q`, reading `u`, writing `v`. -/
  transitions : List (ℕ × List ℕ × List ℕ × ℕ)
  /-- The initial states. -/
  init : List ℕ
  /-- The final states. -/
  final : List ℕ

/-- The alphabet of a code: the letters occurring in the input strings of its
transitions. -/
def codeAlphabet (c : RelCode) : List ℕ := c.transitions.flatMap (fun t => t.2.1)

/-- A string over the alphabet of the code. -/
def CodeWord (c : RelCode) (w : List ℕ) : Prop := ∀ x ∈ w, x ∈ codeAlphabet c

end Lax132576.TransducerCodes
end
