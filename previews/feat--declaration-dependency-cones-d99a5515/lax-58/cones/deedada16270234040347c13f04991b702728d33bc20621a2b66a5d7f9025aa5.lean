-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic

-- Lax13.Ram
section
namespace Lax13
end Lax13

namespace Lax13.Ram
end Lax13.Ram

namespace Lax13.Ram.Instr
end Lax13.Ram.Instr

namespace Lax13.Ram.State
end Lax13.Ram.State

namespace Lax13.Ram.run
end Lax13.Ram.run

namespace Lax13.Ram.Instr.add
end Lax13.Ram.Instr.add

namespace Lax13.Ram.Instr.and
end Lax13.Ram.Instr.and

namespace Lax13.Ram.Instr.div
end Lax13.Ram.Instr.div

namespace Lax13.Ram.Instr.effect
end Lax13.Ram.Instr.effect

namespace Lax13.Ram.Instr.halt
end Lax13.Ram.Instr.halt

namespace Lax13.Ram.Instr.jump
end Lax13.Ram.Instr.jump

namespace Lax13.Ram.Instr.jzero
end Lax13.Ram.Instr.jzero

namespace Lax13.Ram.Instr.load
end Lax13.Ram.Instr.load

namespace Lax13.Ram.Instr.mul
end Lax13.Ram.Instr.mul

namespace Lax13.Ram.Instr.not
end Lax13.Ram.Instr.not

namespace Lax13.Ram.Instr.read
end Lax13.Ram.Instr.read

namespace Lax13.Ram.Instr.set
end Lax13.Ram.Instr.set

namespace Lax13.Ram.Instr.shiftl
end Lax13.Ram.Instr.shiftl

namespace Lax13.Ram.Instr.store
end Lax13.Ram.Instr.store

namespace Lax13.Ram.Instr.sub
end Lax13.Ram.Instr.sub

namespace Lax13.Ram.Instr.write
end Lax13.Ram.Instr.write
end

-- Lax13.RamComputes
section
namespace Lax13.RamComputes
end Lax13.RamComputes
end

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

/-- The distinguished Lax-13 input tape: root, followed by all arena words. -/
def toInput (I : WordImage) : List Nat := I.root :: I.memory.toList

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

end Lax58.WordArena
end

-- Lax58.RamComplexity
section
namespace Lax58.RamComplexity

open Lax13.Ram Lax13.RamComputes

open Lax58.StructuralPresentation Lax58.WordArena

universe u v

/-- A structured result uses the same root-plus-arena convention as input. -/
def arenaOutput {α : Type u} (raw : α → Raw) (x : α) : List Nat :=
  (encodeRaw (raw x)).toInput

end Lax58.RamComplexity
end
