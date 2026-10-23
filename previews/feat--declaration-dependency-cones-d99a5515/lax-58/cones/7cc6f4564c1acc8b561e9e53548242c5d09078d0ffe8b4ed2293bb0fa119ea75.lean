-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f



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

-- Lax58.WordArena
section
namespace Lax58.WordArena.encodeInto
end Lax58.WordArena.encodeInto

namespace Lax58.WordArena.WordImage.ChildAddress
end Lax58.WordArena.WordImage.ChildAddress

namespace Lax58.WordArena.WordImage.ReachableFrom
end Lax58.WordArena.WordImage.ReachableFrom

namespace Lax58.WordArena

open Lax58.StructuralPresentation

universe u

/-- A finite array of unbounded natural-number words. -/
abbrev WordMemory := Array Nat

/-- A closed word array together with its distinguished root address. -/
structure WordImage where
  memory : WordMemory
  root : Nat
  deriving DecidableEq

namespace WordImage

/-- Number of words in the memory array. -/
def memoryWords (I : WordImage) : Nat := I.memory.size

/-- The word at an in-bounds arena address. -/
def wordAt? (I : WordImage) (address : Nat) : Option Nat :=
  I.memory[address]?

/-- Start of a complete aligned three-word arena block. -/
def ValidAddress (I : WordImage) (address : Nat) : Prop :=
  address % 3 = 0 ∧ address + 2 < I.memoryWords

/-- Tag of a natural-payload block. -/
def natTag : Nat := 0

/-- Tag of a binary-pair block. -/
def pairTag : Nat := 1

/-- A block rooted at an address semantically represents a structural value. -/
inductive Represents (I : WordImage) : Nat → Raw → Prop where
  | nat {address payload : Nat}
      (address_valid : I.ValidAddress address)
      (tag : I.wordAt? address = some natTag)
      (value : I.wordAt? (address + 1) = some payload)
      (padding : I.wordAt? (address + 2) = some 0) :
      I.Represents address (.nat payload)
  | pair {address leftAddress rightAddress : Nat} {left right : Raw}
      (address_valid : I.ValidAddress address)
      (tag : I.wordAt? address = some pairTag)
      (left_reference : I.wordAt? (address + 1) = some leftAddress)
      (right_reference : I.wordAt? (address + 2) = some rightAddress)
      (left_value : I.Represents leftAddress left)
      (right_value : I.Represents rightAddress right) :
      I.Represents address (.pair left right)

/-- Every aligned block is meaningful and all child references are valid. -/
def BlocksWellFormed (I : WordImage) : Prop :=
  I.memoryWords % 3 = 0 ∧
    ∀ address, I.ValidAddress address → ∃ raw, I.Represents address raw

end WordImage

end Lax58.WordArena
end
