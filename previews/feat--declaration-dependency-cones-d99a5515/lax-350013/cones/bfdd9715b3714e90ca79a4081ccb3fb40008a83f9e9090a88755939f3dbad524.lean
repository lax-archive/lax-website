-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d



-- Lax350013.WordRAM
section
namespace Lax350013
end Lax350013

namespace Lax350013.WordRAM
end Lax350013.WordRAM

namespace Lax350013.WordRAM.Instr
end Lax350013.WordRAM.Instr

namespace Lax350013.WordRAM.exec
end Lax350013.WordRAM.exec

namespace Lax350013.WordRAM.Instr.accept
end Lax350013.WordRAM.Instr.accept

namespace Lax350013.WordRAM.Instr.add
end Lax350013.WordRAM.Instr.add

namespace Lax350013.WordRAM.Instr.bltz
end Lax350013.WordRAM.Instr.bltz

namespace Lax350013.WordRAM.Instr.load
end Lax350013.WordRAM.Instr.load

namespace Lax350013.WordRAM.Instr.mul
end Lax350013.WordRAM.Instr.mul

namespace Lax350013.WordRAM.Instr.one
end Lax350013.WordRAM.Instr.one

namespace Lax350013.WordRAM.Instr.reject
end Lax350013.WordRAM.Instr.reject

namespace Lax350013.WordRAM.Instr.store
end Lax350013.WordRAM.Instr.store

namespace Lax350013.WordRAM.Instr.sub
end Lax350013.WordRAM.Instr.sub
end

-- Lax350013.PolynomialTime
section
namespace Lax350013.PolynomialTime.Problem
end Lax350013.PolynomialTime.Problem

namespace Lax350013.PolynomialTime

open Lax350013.WordRAM

/-- `T(n) = O(n^r)`, both sides raised to the power `r.den`: core Lean has no fractional powers. For `r = 1.9992 =
2499/1250` it says `T(n)^1250 ≤ K n^2499`. -/
def BigO (T : Nat → Nat) (r : Rat) : Prop :=
  ∃ K : Nat, ∀ n ≥ 2, T n ^ r.den ≤ K * n ^ r.num.toNat

end Lax350013.PolynomialTime
end
