-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d



-- Lax560851.StructuralPresentation
section
namespace Lax560851.StructuralPresentation.Raw.nodes
end Lax560851.StructuralPresentation.Raw.nodes

namespace Lax560851.StructuralPresentation

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

end Lax560851.StructuralPresentation
end

-- Lax560851.WordArena
section
namespace Lax560851.WordArena.WordImage.Represents
end Lax560851.WordArena.WordImage.Represents

namespace Lax560851.WordArena

open Lax560851.StructuralPresentation

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

/-- A pair block directly refers to one valid child block. -/
inductive ChildAddress (I : WordImage) : Nat → Nat → Prop where
  | left {parent child : Nat}
      (parent_valid : I.ValidAddress parent)
      (child_valid : I.ValidAddress child)
      (tag : I.wordAt? parent = some pairTag)
      (reference : I.wordAt? (parent + 1) = some child) :
      I.ChildAddress parent child
  | right {parent child : Nat}
      (parent_valid : I.ValidAddress parent)
      (child_valid : I.ValidAddress child)
      (tag : I.wordAt? parent = some pairTag)
      (reference : I.wordAt? (parent + 2) = some child) :
      I.ChildAddress parent child

/-- Addresses reachable from a chosen root by following child references. -/
inductive ReachableFrom (I : WordImage) (root : Nat) : Nat → Prop where
  | root : I.ReachableFrom root root
  | child {parent child : Nat}
      (parent_reachable : I.ReachableFrom root parent)
      (child_address : I.ChildAddress parent child) :
      I.ReachableFrom root child

/-- Every complete block is reachable from the distinguished root. -/
def Dense (I : WordImage) : Prop :=
  ∀ address, I.ValidAddress address → I.ReachableFrom I.root address

end WordImage

/-- Append the postorder arena of a raw value and return its root address. -/
def encodeInto : Raw → WordMemory → WordMemory × Nat
  | .nat payload, memory =>
      let address := memory.size
      (memory.push WordImage.natTag |>.push payload |>.push 0, address)
  | .pair left right, memory =>
      let (memory, leftAddress) := encodeInto left memory
      let (memory, rightAddress) := encodeInto right memory
      let address := memory.size
      (memory.push WordImage.pairTag |>.push leftAddress |>.push rightAddress, address)

/-- Distinguished closed postorder arena of a structural value. -/
def encodeRaw (raw : Raw) : WordImage :=
  let (memory, root) := encodeInto raw #[]
  { memory, root }

axiom encodeRaw_dense (raw : Raw) :
  (encodeRaw raw).Dense

end Lax560851.WordArena
end
