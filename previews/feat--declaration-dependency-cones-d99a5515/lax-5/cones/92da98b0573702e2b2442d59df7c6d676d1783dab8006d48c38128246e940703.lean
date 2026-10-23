-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Logic.Embedding.Basic
import Mathlib.ModelTheory.Semantics

-- Lax5.Transductions
section
namespace Lax5.Transductions.colorStructure
end Lax5.Transductions.colorStructure

namespace Lax5.Transductions

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

/-- The language `L` expanded by `k` unary color predicates. -/
abbrev withColors (L : Language.{u, v}) (k : ℕ) : Language :=
  L.sum (colorLanguage k)

/-- A non-copying transduction from `L`-structures to `L'`-structures:
finitely many unary colors, a domain formula selecting the output
universe, and one formula per relation symbol of the target language. -/
structure Transduction (L : Language.{u, v}) (L' : Language.{u', v'}) where
  /-- The number of unary color predicates. -/
  colors : ℕ
  /-- The formula selecting the elements of the output structure. -/
  domain : (withColors L colors).Formula (Fin 1)
  /-- The formula interpreting each relation symbol of the target. -/
  rel : ∀ {r : ℕ}, L'.Relations r → (withColors L colors).Formula (Fin r)

end Lax5.Transductions
end
