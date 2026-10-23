-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f



-- Lax58.StructuralPresentation
section
namespace Lax58
end Lax58

namespace Lax58.StructuralPresentation
end Lax58.StructuralPresentation

namespace Lax58.StructuralPresentation.Presentation
end Lax58.StructuralPresentation.Presentation

namespace Lax58.StructuralPresentation.Raw
end Lax58.StructuralPresentation.Raw

namespace Lax58.StructuralPresentation.Raw.nat
end Lax58.StructuralPresentation.Raw.nat

namespace Lax58.StructuralPresentation.Raw.nodes
end Lax58.StructuralPresentation.Raw.nodes

namespace Lax58.StructuralPresentation.Raw.pair
end Lax58.StructuralPresentation.Raw.pair
end

-- Lax58.WordArena
section
namespace Lax58.WordArena.encodeInto
end Lax58.WordArena.encodeInto

namespace Lax58.WordArena.WordImage.ChildAddress
end Lax58.WordArena.WordImage.ChildAddress

namespace Lax58.WordArena.WordImage.ReachableFrom
end Lax58.WordArena.WordImage.ReachableFrom

namespace Lax58.WordArena.WordImage.Represents
end Lax58.WordArena.WordImage.Represents

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

/-- The distinguished Lax-13 input tape: root, followed by all arena words. -/
def toInput (I : WordImage) : List Nat := I.root :: I.memory.toList

/-- The memory array fits in the address space of `w`-bit words. -/
def AddressSpaceFits (I : WordImage) (w : Nat) : Prop :=
  I.memoryWords ≤ 2 ^ w

/-- Every supplied word, including the root, fits in `w` bits. -/
def ValuesFitInWord (I : WordImage) (w : Nat) : Prop :=
  ∀ x ∈ I.toInput, x < 2 ^ w

/-- Both the address space and all supplied word values fit at width `w`. -/
def FitsInWord (I : WordImage) (w : Nat) : Prop :=
  I.AddressSpaceFits w ∧ I.ValuesFitInWord w

end WordImage

end Lax58.WordArena
end
