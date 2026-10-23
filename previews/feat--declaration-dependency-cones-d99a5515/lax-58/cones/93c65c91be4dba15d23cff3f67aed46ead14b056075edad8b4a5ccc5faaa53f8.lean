-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f



-- Lax58.StructuralPresentation
section
namespace Lax58.StructuralPresentation

universe u

/-- The universal shape of structurally finite data. -/
inductive Raw where
  | nat : Nat → Raw
  | pair : Raw → Raw → Raw
  deriving DecidableEq

namespace Raw

/-- Number of nodes in a universal structural representation. -/
def nodes : Raw → Nat
  | .nat _ => 1
  | .pair a b => nodes a + nodes b + 1

/-- Largest natural-number payload occurring in a representation. -/
def maxNat : Raw → Nat
  | .nat n => n
  | .pair a b => max a.maxNat b.maxNat

/-- Every natural payload in a representation fits into a `w`-bit word. -/
def PayloadsFitInWord (raw : Raw) (w : Nat) : Prop :=
  raw.maxNat < 2 ^ w

end Raw

namespace Presentation

end Presentation

end Lax58.StructuralPresentation
end
