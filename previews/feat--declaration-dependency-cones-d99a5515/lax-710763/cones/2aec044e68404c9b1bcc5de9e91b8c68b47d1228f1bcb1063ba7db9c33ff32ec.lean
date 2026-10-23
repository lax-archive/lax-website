-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Embedding.Basic
import Mathlib.ModelTheory.Semantics

-- Lax710763.Transductions
section
namespace Lax710763.Transductions.Transduction
end Lax710763.Transductions.Transduction

namespace Lax710763.Transductions.colorStructure
end Lax710763.Transductions.colorStructure

namespace Lax710763.Transductions

open FirstOrder

universe u v u' v'

/-- The relation symbols of the color language: `k` unary predicates. -/
inductive ColorRel (k : ℕ) : ℕ → Type
  | color (i : Fin k) : ColorRel k 1

end Lax710763.Transductions
end
