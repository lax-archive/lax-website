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

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

namespace Presentation

/-- Structural size before any serialization or memory layout is chosen. -/
def structuralSize {α : Type u} (P : Presentation α) (x : α) : Nat :=
  (P.toRaw x).nodes

/-- Every natural payload of a value fits into a `w`-bit word. -/
def PayloadsFitInWord {α : Type u}
    (P : Presentation α) (x : α) (w : Nat) : Prop :=
  (P.toRaw x).PayloadsFitInWord w

end Presentation

end Lax58.StructuralPresentation
end

-- Lax58.WordArena
section
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

/-- Tag of a natural-payload block. -/
def natTag : Nat := 0

/-- Tag of a binary-pair block. -/
def pairTag : Nat := 1

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

/-- Distinguished arena of a value through a named structural presentation. -/
def encode {α : Type u} (P : Presentation α) (x : α) : WordImage :=
  encodeRaw (P.toRaw x)

axiom encode_fits {α : Type u} (P : Presentation α) (x : α) (w : Nat) :
  P.PayloadsFitInWord x w →
  3 * P.structuralSize x ≤ 2 ^ w →
  (encode P x).FitsInWord w

end Lax58.WordArena
end
