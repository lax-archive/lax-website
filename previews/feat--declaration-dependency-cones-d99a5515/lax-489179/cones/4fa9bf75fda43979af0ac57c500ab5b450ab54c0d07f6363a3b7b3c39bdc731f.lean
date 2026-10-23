-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.SetTheory.Cardinal.Finite

-- Lax489179.Algorithms
section
namespace Lax489179
end Lax489179

namespace Lax489179.Algorithms
end Lax489179.Algorithms

namespace Lax489179.Algorithms.Mode
end Lax489179.Algorithms.Mode

namespace Lax489179.Algorithms.Mode.deterministic
end Lax489179.Algorithms.Mode.deterministic

namespace Lax489179.Algorithms.Mode.randomized
end Lax489179.Algorithms.Mode.randomized
end

-- Lax808846.Ram
section
namespace Lax808846.Ram.Instr
end Lax808846.Ram.Instr

namespace Lax808846.Ram.run
end Lax808846.Ram.run

namespace Lax808846.Ram.Instr.add
end Lax808846.Ram.Instr.add

namespace Lax808846.Ram.Instr.and
end Lax808846.Ram.Instr.and

namespace Lax808846.Ram.Instr.div
end Lax808846.Ram.Instr.div

namespace Lax808846.Ram.Instr.effect
end Lax808846.Ram.Instr.effect

namespace Lax808846.Ram.Instr.halt
end Lax808846.Ram.Instr.halt

namespace Lax808846.Ram.Instr.inputLength
end Lax808846.Ram.Instr.inputLength

namespace Lax808846.Ram.Instr.inputLoad
end Lax808846.Ram.Instr.inputLoad

namespace Lax808846.Ram.Instr.jeof
end Lax808846.Ram.Instr.jeof

namespace Lax808846.Ram.Instr.jump
end Lax808846.Ram.Instr.jump

namespace Lax808846.Ram.Instr.jzero
end Lax808846.Ram.Instr.jzero

namespace Lax808846.Ram.Instr.load
end Lax808846.Ram.Instr.load

namespace Lax808846.Ram.Instr.mul
end Lax808846.Ram.Instr.mul

namespace Lax808846.Ram.Instr.not
end Lax808846.Ram.Instr.not

namespace Lax808846.Ram.Instr.read
end Lax808846.Ram.Instr.read

namespace Lax808846.Ram.Instr.set
end Lax808846.Ram.Instr.set

namespace Lax808846.Ram.Instr.shiftl
end Lax808846.Ram.Instr.shiftl

namespace Lax808846.Ram.Instr.store
end Lax808846.Ram.Instr.store

namespace Lax808846.Ram.Instr.sub
end Lax808846.Ram.Instr.sub

namespace Lax808846.Ram.Instr.write
end Lax808846.Ram.Instr.write

namespace Lax808846.Ram

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

end Lax808846.Ram
end

-- Lax489179.WordPrograms
section
namespace Lax489179.WordPrograms.Instruction
end Lax489179.WordPrograms.Instruction

namespace Lax489179.WordPrograms.run
end Lax489179.WordPrograms.run

namespace Lax489179.WordPrograms.step
end Lax489179.WordPrograms.step

namespace Lax489179.WordPrograms.Instruction.coin
end Lax489179.WordPrograms.Instruction.coin

namespace Lax489179.WordPrograms.Instruction.ordinary
end Lax489179.WordPrograms.Instruction.ordinary

namespace Lax489179.WordPrograms

open Lax808846.Ram

structure Config where
  state : State
  halted : Bool

end Lax489179.WordPrograms
end
