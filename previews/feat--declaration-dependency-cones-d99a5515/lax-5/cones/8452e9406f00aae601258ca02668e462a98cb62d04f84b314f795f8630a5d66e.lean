-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Logic.Embedding.Basic
import Mathlib.ModelTheory.Semantics

-- Lax5.Transductions
section
namespace Lax5.Transductions.Transduction
end Lax5.Transductions.Transduction

namespace Lax5.Transductions.colorStructure
end Lax5.Transductions.colorStructure

namespace Lax5.Transductions

open FirstOrder

universe u v u' v'

/-- The relation symbols of the color language: `k` unary predicates. -/
inductive ColorRel (k : ℕ) : ℕ → Type
  | color (i : Fin k) : ColorRel k 1

end Lax5.Transductions
end
