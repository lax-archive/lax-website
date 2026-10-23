-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Embedding.Basic
import Mathlib.ModelTheory.Semantics

-- Lax710763.Transductions
section
namespace Lax710763.Transductions.Transduction
end Lax710763.Transductions.Transduction

namespace Lax710763.Transductions

open FirstOrder

universe u v u' v'

/-- The relation symbols of the color language: `k` unary predicates. -/
inductive ColorRel (k : ℕ) : ℕ → Type
  | color (i : Fin k) : ColorRel k 1

/-- The language consisting of `k` unary color predicates and nothing
else. -/
def colorLanguage (k : ℕ) : Language :=
  ⟨fun _ => Empty, ColorRel k⟩
  deriving Language.IsRelational

/-- The color sets `colors` as a structure of the color language:
`.color i` holds of the elements of `colors i`. -/
@[implicit_reducible]
def colorStructure {M : Type*} {k : ℕ} (colors : Fin k → Set M) :
    (colorLanguage k).Structure M where
  RelMap | .color i => fun x => x 0 ∈ colors i

end Lax710763.Transductions
end
