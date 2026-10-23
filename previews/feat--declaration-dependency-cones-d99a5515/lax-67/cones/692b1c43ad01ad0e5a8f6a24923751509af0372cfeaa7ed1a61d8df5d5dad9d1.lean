-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.List.Basic

-- Lax67.Ram
section
namespace Lax67.Ram.Instr
end Lax67.Ram.Instr

namespace Lax67.Ram.State
end Lax67.Ram.State

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

/-- The memory `m` with cell `a` set to `v`, at word length `w`: the
address and the value written are both taken modulo `2 ^ w`. -/
def setCell (w : ℕ) (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun b => if b = a % 2 ^ w then v % 2 ^ w else m b

end Lax67.Ram
end
