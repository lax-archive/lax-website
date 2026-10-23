-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.List.Basic

-- Lax13.Ram
section
namespace Lax13.Ram.Instr
end Lax13.Ram.Instr

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

namespace Lax13.Ram

/-- A machine state: the program counter, the contents of every memory
cell, the part of the input tape not yet read, and the output tape
written so far. Memory is the only storage there is. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The contents of the memory cells; only the cells with number below
  `2 ^ w` are ever addressed. -/
  mem : ℕ → ℕ
  /-- The numbers still to be read from the input tape. -/
  inp : List ℕ
  /-- The numbers written to the output tape so far. -/
  out : List ℕ

/-- The initial state on input `x`: program counter zero, all memory
cells zero, the input word on the input tape, the output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  mem := fun _ => 0
  inp := x
  out := []

end Lax13.Ram
end
