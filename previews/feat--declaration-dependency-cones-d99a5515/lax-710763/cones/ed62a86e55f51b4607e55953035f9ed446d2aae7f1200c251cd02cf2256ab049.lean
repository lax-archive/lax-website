-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Embedding.Basic
import Mathlib.ModelTheory.Semantics

-- Lax710763.Transductions
section
namespace Lax710763.Transductions.ColorRel
end Lax710763.Transductions.ColorRel

namespace Lax710763.Transductions.Transduction
end Lax710763.Transductions.Transduction

namespace Lax710763.Transductions.colorStructure
end Lax710763.Transductions.colorStructure

namespace Lax710763.Transductions.ColorRel.color
end Lax710763.Transductions.ColorRel.color

namespace Lax710763.Transductions

open FirstOrder

universe u v u' v'

/-- A class of finite structures of the language `L`: for each `n`, a
predicate on the `L`-structures over the canonical `n`-element type. -/
abbrev StructureClass (L : Language.{u, v}) : Type (max u v) :=
  ∀ n : ℕ, L.Structure (Fin n) → Prop

end Lax710763.Transductions
end
