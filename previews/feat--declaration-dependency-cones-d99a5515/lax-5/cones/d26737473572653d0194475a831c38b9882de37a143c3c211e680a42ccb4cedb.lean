-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Logic.Embedding.Basic
import Mathlib.ModelTheory.Semantics

-- Lax5.Transductions
section
namespace Lax5.Transductions.ColorRel
end Lax5.Transductions.ColorRel

namespace Lax5.Transductions.Transduction
end Lax5.Transductions.Transduction

namespace Lax5.Transductions.colorStructure
end Lax5.Transductions.colorStructure

namespace Lax5.Transductions.ColorRel.color
end Lax5.Transductions.ColorRel.color

namespace Lax5.Transductions

open FirstOrder

universe u v u' v'

/-- A class of finite structures of the language `L`: for each `n`, a
predicate on the `L`-structures over the canonical `n`-element type. -/
abbrev StructureClass (L : Language.{u, v}) : Type (max u v) :=
  ∀ n : ℕ, L.Structure (Fin n) → Prop

end Lax5.Transductions
end
