-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax496464.FlowShop
section
namespace Lax496464
end Lax496464

namespace Lax496464.FlowShop
end Lax496464.FlowShop

namespace Lax496464.FlowShop.Instance
end Lax496464.FlowShop.Instance

namespace Lax496464.FlowShop.Instance.JITSchedule
end Lax496464.FlowShop.Instance.JITSchedule
end

-- Lax496464.BinaryEncoding
section
namespace Lax496464.BinaryEncoding

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax434930.PolynomialTime

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. The unary prefix makes the code self-delimiting. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

end Lax496464.BinaryEncoding
end
