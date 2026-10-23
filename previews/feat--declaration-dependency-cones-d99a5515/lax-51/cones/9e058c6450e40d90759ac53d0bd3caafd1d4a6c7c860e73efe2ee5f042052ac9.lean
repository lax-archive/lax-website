-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype

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

-- Lax51.BinaryWordEncoding
section
namespace Lax51
end Lax51

namespace Lax51.BinaryWordEncoding
end Lax51.BinaryWordEncoding

namespace Lax51.BinaryWordEncoding.Symbol
end Lax51.BinaryWordEncoding.Symbol

namespace Lax51.BinaryWordEncoding.Symbol.one
end Lax51.BinaryWordEncoding.Symbol.one

namespace Lax51.BinaryWordEncoding.Symbol.separator
end Lax51.BinaryWordEncoding.Symbol.separator

namespace Lax51.BinaryWordEncoding.Symbol.zero
end Lax51.BinaryWordEncoding.Symbol.zero
end

-- Lax51.RamPolytime
section
namespace Lax51.RamPolytime

open Lax13.Ram

open Lax51.BinaryWordEncoding

/-- Every entry of `x` is representable by a word of `w` bits. -/
def FitsInWords (w : ℕ) (x : List ℕ) : Prop :=
  ∀ a ∈ x, a < 2 ^ w

end Lax51.RamPolytime
end
