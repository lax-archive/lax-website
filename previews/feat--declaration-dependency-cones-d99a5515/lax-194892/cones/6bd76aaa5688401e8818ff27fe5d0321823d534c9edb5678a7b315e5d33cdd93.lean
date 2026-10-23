-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

-- Lax194892.ForTransducers
section
namespace Lax194892.ForTransducers.ForProg.LoopFree
end Lax194892.ForTransducers.ForProg.LoopFree

namespace Lax194892.ForTransducers.ForProg.assign
end Lax194892.ForTransducers.ForProg.assign

namespace Lax194892.ForTransducers.ForProg.exec
end Lax194892.ForTransducers.ForProg.exec

namespace Lax194892.ForTransducers.ForProg.ite
end Lax194892.ForTransducers.ForProg.ite

namespace Lax194892.ForTransducers.ForProg.loop
end Lax194892.ForTransducers.ForProg.loop

namespace Lax194892.ForTransducers.ForProg.nestLoops
end Lax194892.ForTransducers.ForProg.nestLoops

namespace Lax194892.ForTransducers.ForProg.output
end Lax194892.ForTransducers.ForProg.output

namespace Lax194892.ForTransducers.ForProg.seq
end Lax194892.ForTransducers.ForProg.seq

namespace Lax194892.ForTransducers.ForProg.skip
end Lax194892.ForTransducers.ForProg.skip

namespace Lax194892.ForTransducers.ForTest.Holds
end Lax194892.ForTransducers.ForTest.Holds

namespace Lax194892.ForTransducers.ForTest.and
end Lax194892.ForTransducers.ForTest.and

namespace Lax194892.ForTransducers.ForTest.boolVar
end Lax194892.ForTransducers.ForTest.boolVar

namespace Lax194892.ForTransducers.ForTest.eqPos
end Lax194892.ForTransducers.ForTest.eqPos

namespace Lax194892.ForTransducers.ForTest.label
end Lax194892.ForTransducers.ForTest.label

namespace Lax194892.ForTransducers.ForTest.lePos
end Lax194892.ForTransducers.ForTest.lePos

namespace Lax194892.ForTransducers.ForTest.not
end Lax194892.ForTransducers.ForTest.not

namespace Lax194892.ForTransducers.ForTest.or
end Lax194892.ForTransducers.ForTest.or

namespace Lax194892.ForTransducers

namespace ForTest

variable {A : Type}

end ForTest

/-- Running the body of a loop over a list of positions, threading the Boolean
valuation and concatenating the outputs. -/
def forLoopRun {B : Type} (body : (ℕ → Bool) → ℕ → (ℕ → Bool) × List B) :
    List ℕ → (ℕ → Bool) → (ℕ → Bool) × List B
  | [], bv => (bv, [])
  | p :: ps, bv =>
      let r := body bv p
      let r' := forLoopRun body ps r.1
      (r'.1, r.2 ++ r'.2)

namespace ForProg

variable {A B : Type}

end ForProg

end Lax194892.ForTransducers
end
