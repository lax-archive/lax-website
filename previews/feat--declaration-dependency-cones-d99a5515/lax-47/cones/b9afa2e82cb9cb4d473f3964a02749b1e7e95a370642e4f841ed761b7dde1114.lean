-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype

-- Lax759944.BinaryWordEncoding
section
namespace Lax759944
end Lax759944

namespace Lax759944.BinaryWordEncoding
end Lax759944.BinaryWordEncoding

namespace Lax759944.BinaryWordEncoding.Symbol
end Lax759944.BinaryWordEncoding.Symbol

namespace Lax759944.BinaryWordEncoding.Symbol.one
end Lax759944.BinaryWordEncoding.Symbol.one

namespace Lax759944.BinaryWordEncoding.Symbol.separator
end Lax759944.BinaryWordEncoding.Symbol.separator

namespace Lax759944.BinaryWordEncoding.Symbol.zero
end Lax759944.BinaryWordEncoding.Symbol.zero
end

-- Lax759944.TuringPolytime
section
namespace Lax759944.TuringPolytime
end Lax759944.TuringPolytime
end

-- Lax47.Machine
section
namespace Lax47.Machine.PolytimeProgram
end Lax47.Machine.PolytimeProgram

namespace Lax47.Machine.RandomSeed
end Lax47.Machine.RandomSeed

set_option autoImplicit false

namespace Lax47.Machine

open Lax759944.BinaryWordEncoding Lax759944.TuringPolytime

/-- Encode one Boolean as a natural-number word. -/
def bitWord (bit : Bool) : ℕ :=
  if bit then 1 else 0

end Lax47.Machine
end
