-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.List.Basic

-- Lax67.Ram
section
namespace Lax67.Ram.Instr
end Lax67.Ram.Instr

namespace Lax67.Ram.run
end Lax67.Ram.run

namespace Lax67.Ram.Instr.add
end Lax67.Ram.Instr.add

namespace Lax67.Ram.Instr.and
end Lax67.Ram.Instr.and

namespace Lax67.Ram.Instr.div
end Lax67.Ram.Instr.div

namespace Lax67.Ram.Instr.effect
end Lax67.Ram.Instr.effect

namespace Lax67.Ram.Instr.halt
end Lax67.Ram.Instr.halt

namespace Lax67.Ram.Instr.inputLength
end Lax67.Ram.Instr.inputLength

namespace Lax67.Ram.Instr.inputLoad
end Lax67.Ram.Instr.inputLoad

namespace Lax67.Ram.Instr.jeof
end Lax67.Ram.Instr.jeof

namespace Lax67.Ram.Instr.jump
end Lax67.Ram.Instr.jump

namespace Lax67.Ram.Instr.jzero
end Lax67.Ram.Instr.jzero

namespace Lax67.Ram.Instr.load
end Lax67.Ram.Instr.load

namespace Lax67.Ram.Instr.mul
end Lax67.Ram.Instr.mul

namespace Lax67.Ram.Instr.not
end Lax67.Ram.Instr.not

namespace Lax67.Ram.Instr.read
end Lax67.Ram.Instr.read

namespace Lax67.Ram.Instr.set
end Lax67.Ram.Instr.set

namespace Lax67.Ram.Instr.shiftl
end Lax67.Ram.Instr.shiftl

namespace Lax67.Ram.Instr.store
end Lax67.Ram.Instr.store

namespace Lax67.Ram.Instr.sub
end Lax67.Ram.Instr.sub

namespace Lax67.Ram.Instr.write
end Lax67.Ram.Instr.write

namespace Lax67.Ram

/-- A machine state: the program counter, the contents of every memory
cell, the immutable original input array, the remaining sequential input
tape, and the output tape written so far. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The contents of the memory cells; only the cells with number below
  `2 ^ w` are ever addressed. -/
  mem : ℕ → ℕ
  /-- The original read-only input, unchanged by every instruction. -/
  input : List ℕ
  /-- The numbers still to be read from the input tape. -/
  inp : List ℕ
  /-- The numbers written to the output tape so far. -/
  out : List ℕ

/-- The initial state on input `x`: program counter zero, all memory
cells zero, the original input array and its sequential tape both `x`,
and the output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  mem := fun _ => 0
  input := x
  inp := x
  out := []

end Lax67.Ram
end
