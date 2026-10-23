-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
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

-- Lax489179.TuringMachine
section
namespace Lax489179.TuringMachine.Config
end Lax489179.TuringMachine.Config

namespace Lax489179.TuringMachine.Machine
end Lax489179.TuringMachine.Machine

namespace Lax489179.TuringMachine.init
end Lax489179.TuringMachine.init

namespace Lax489179.TuringMachine.run
end Lax489179.TuringMachine.run

namespace Lax489179.TuringMachine.step
end Lax489179.TuringMachine.step

namespace Lax489179.TuringMachine.Move.offset
end Lax489179.TuringMachine.Move.offset

namespace Lax489179.TuringMachine

inductive Move
  | left
  | stay
  | right

inductive Instruction (tapes symbols states : ℕ)
  | halt (answer : Bool)
  | next (state : Fin states) (write : Fin tapes → Fin symbols)
      (move : Fin tapes → Move)

end Lax489179.TuringMachine
end
