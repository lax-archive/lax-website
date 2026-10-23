-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Nat.Pairing

-- Lax58.StructuralPresentation
section
namespace Lax58.StructuralPresentation.Raw.nodes
end Lax58.StructuralPresentation.Raw.nodes

namespace Lax58.StructuralPresentation

universe u

/-- The universal shape of structurally finite data. -/
inductive Raw where
  | nat : Nat → Raw
  | pair : Raw → Raw → Raw
  deriving DecidableEq

namespace Raw

end Raw

namespace Presentation

end Presentation

end Lax58.StructuralPresentation
end

-- Lax58.StructuralCombinators
section
namespace Lax58.StructuralCombinators.Derivable
end Lax58.StructuralCombinators.Derivable

namespace Lax58.StructuralCombinators.Generated
end Lax58.StructuralCombinators.Generated

namespace Lax58.StructuralCombinators.Lawful
end Lax58.StructuralCombinators.Lawful

namespace Lax58.StructuralCombinators.SizeLaws
end Lax58.StructuralCombinators.SizeLaws

namespace Lax58.StructuralCombinators.listFromRaw
end Lax58.StructuralCombinators.listFromRaw

namespace Lax58.StructuralCombinators.listToRaw
end Lax58.StructuralCombinators.listToRaw

namespace Lax58.StructuralCombinators.nat
end Lax58.StructuralCombinators.nat

namespace Lax58.StructuralCombinators.prod
end Lax58.StructuralCombinators.prod

namespace Lax58.StructuralCombinators

open Lax58.StructuralPresentation

open Lax58.StructuralPresentation.Presentation

universe u v

namespace Raw

/-- An injective numerical realization of character lists, used only inside
the named-constructor combinator. -/
def constructorCharsCode : List Char → Nat
  | [] => 0
  | c :: cs => Nat.pair c.toNat (constructorCharsCode cs) + 1

/-- The internal numerical realization of a symbolic constructor name. -/
def constructorNameCode (name : String) : Nat :=
  constructorCharsCode name.toList

/-- Structural representation of an ordered list of already represented fields. -/
def fields : List StructuralPresentation.Raw → StructuralPresentation.Raw
  | [] => .nat 0
  | x :: xs => .pair x (fields xs)

/-- A symbolically named constructor occurrence with ordered fields. -/
def constructor (name : String) (xs : List StructuralPresentation.Raw) :
    StructuralPresentation.Raw :=
  .pair (.nat (constructorNameCode name)) (fields xs)

end Raw

end Lax58.StructuralCombinators
end
