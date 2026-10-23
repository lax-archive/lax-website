-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax888481.Scheduling
section
namespace Lax888481
end Lax888481

namespace Lax888481.Scheduling
end Lax888481.Scheduling

namespace Lax888481.Scheduling.Instance
end Lax888481.Scheduling.Instance
end

-- Lax888481.BinaryEncoding
section
namespace Lax888481.BinaryEncoding

open Lax888481.Scheduling Lax434930.PolynomialTime

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. The unary prefix makes the code self-delimiting. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

end Lax888481.BinaryEncoding
end
